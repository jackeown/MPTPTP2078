%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I9gWpOR7Mx

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:45 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 275 expanded)
%              Number of leaves         :   48 ( 107 expanded)
%              Depth                    :   21
%              Number of atoms          : 1324 (3162 expanded)
%              Number of equality atoms :   78 ( 167 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_B ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X28 ) )
      | ( X27 = X28 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ) )
      | ~ ( r2_hidden @ X39 @ X37 )
      | ~ ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','27','34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('57',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('58',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('64',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('69',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('82',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','93'])).

thf('95',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('97',plain,(
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

thf('98',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('99',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('100',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('101',plain,(
    ! [X34: $i] :
      ( ( k3_yellow_1 @ X34 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('102',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v2_waybel_0 @ X35 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X36 ) ) ) )
      | ~ ( v13_waybel_0 @ X35 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X36 ) ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X36 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X36 ) ) ) ) @ X35 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X36 @ ( k3_yellow19 @ X36 @ ( k2_struct_0 @ X36 ) @ X35 ) ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('106',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k4_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('109',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104','107','108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','114'])).

thf('116',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','115'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('117',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('118',plain,
    ( ( sk_B != sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I9gWpOR7Mx
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 10:00:22 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.44/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.70  % Solved by: fo/fo7.sh
% 0.44/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.70  % done 537 iterations in 0.214s
% 0.44/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.70  % SZS output start Refutation
% 0.44/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.44/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.44/0.70  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.44/0.70  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.44/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.70  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.44/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.70  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.44/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.70  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.44/0.70  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.44/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.70  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.44/0.70  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.44/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.70  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.44/0.70  thf(t15_yellow19, conjecture,
% 0.44/0.70    (![A:$i]:
% 0.44/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.44/0.70       ( ![B:$i]:
% 0.44/0.70         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.70             ( v1_subset_1 @
% 0.44/0.70               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.44/0.70             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.70             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.70             ( m1_subset_1 @
% 0.44/0.70               B @ 
% 0.44/0.70               ( k1_zfmisc_1 @
% 0.44/0.70                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.44/0.70           ( ( B ) =
% 0.44/0.70             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.44/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.70    (~( ![A:$i]:
% 0.44/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.44/0.70          ( ![B:$i]:
% 0.44/0.70            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.70                ( v1_subset_1 @
% 0.44/0.70                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.44/0.70                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.70                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.70                ( m1_subset_1 @
% 0.44/0.70                  B @ 
% 0.44/0.70                  ( k1_zfmisc_1 @
% 0.44/0.70                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.44/0.70              ( ( B ) =
% 0.44/0.70                ( k2_yellow19 @
% 0.44/0.70                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.44/0.70    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.44/0.70  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf(t3_xboole_0, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.44/0.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.70            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.44/0.70  thf('1', plain,
% 0.44/0.70      (![X6 : $i, X7 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.70  thf(t17_zfmisc_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( ( A ) != ( B ) ) =>
% 0.44/0.70       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.44/0.70  thf('2', plain,
% 0.44/0.70      (![X27 : $i, X28 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X28))
% 0.44/0.70          | ((X27) = (X28)))),
% 0.44/0.70      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.44/0.70  thf(l24_zfmisc_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.44/0.70  thf('3', plain,
% 0.44/0.70      (![X25 : $i, X26 : $i]:
% 0.44/0.70         (~ (r1_xboole_0 @ (k1_tarski @ X25) @ X26) | ~ (r2_hidden @ X25 @ X26))),
% 0.44/0.70      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.44/0.70  thf('4', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i]:
% 0.44/0.70         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.70  thf('5', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.44/0.70          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['1', '4'])).
% 0.44/0.70  thf('6', plain,
% 0.44/0.70      (![X6 : $i, X7 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.70  thf(d3_struct_0, axiom,
% 0.44/0.70    (![A:$i]:
% 0.44/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.44/0.70  thf('7', plain,
% 0.44/0.70      (![X32 : $i]:
% 0.44/0.70         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.44/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.70  thf('8', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_B @ 
% 0.44/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf(d2_yellow_1, axiom,
% 0.44/0.70    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.44/0.70  thf('9', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('10', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_B @ 
% 0.44/0.70        (k1_zfmisc_1 @ 
% 0.44/0.70         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.44/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.44/0.70  thf('11', plain,
% 0.44/0.70      (((m1_subset_1 @ sk_B @ 
% 0.44/0.70         (k1_zfmisc_1 @ 
% 0.44/0.70          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.44/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.70      inference('sup+', [status(thm)], ['7', '10'])).
% 0.44/0.70  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('13', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_B @ 
% 0.44/0.70        (k1_zfmisc_1 @ 
% 0.44/0.70         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.44/0.70      inference('demod', [status(thm)], ['11', '12'])).
% 0.44/0.70  thf(t2_yellow19, axiom,
% 0.44/0.70    (![A:$i]:
% 0.44/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.70       ( ![B:$i]:
% 0.44/0.70         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.70             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.44/0.70             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.44/0.70             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.44/0.70             ( m1_subset_1 @
% 0.44/0.70               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.44/0.70           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.44/0.70  thf('14', plain,
% 0.44/0.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.44/0.70         ((v1_xboole_0 @ X37)
% 0.44/0.70          | ~ (v1_subset_1 @ X37 @ (u1_struct_0 @ (k3_yellow_1 @ X38)))
% 0.44/0.70          | ~ (v2_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.44/0.70          | ~ (v13_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.44/0.70          | ~ (m1_subset_1 @ X37 @ 
% 0.44/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X38))))
% 0.44/0.70          | ~ (r2_hidden @ X39 @ X37)
% 0.44/0.70          | ~ (v1_xboole_0 @ X39)
% 0.44/0.70          | (v1_xboole_0 @ X38))),
% 0.44/0.70      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.44/0.70  thf('15', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('16', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('17', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('18', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('19', plain,
% 0.44/0.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.44/0.70         ((v1_xboole_0 @ X37)
% 0.44/0.70          | ~ (v1_subset_1 @ X37 @ 
% 0.44/0.70               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X38))))
% 0.44/0.70          | ~ (v2_waybel_0 @ X37 @ (k3_lattice3 @ (k1_lattice3 @ X38)))
% 0.44/0.70          | ~ (v13_waybel_0 @ X37 @ (k3_lattice3 @ (k1_lattice3 @ X38)))
% 0.44/0.70          | ~ (m1_subset_1 @ X37 @ 
% 0.44/0.70               (k1_zfmisc_1 @ 
% 0.44/0.70                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X38)))))
% 0.44/0.70          | ~ (r2_hidden @ X39 @ X37)
% 0.44/0.70          | ~ (v1_xboole_0 @ X39)
% 0.44/0.70          | (v1_xboole_0 @ X38))),
% 0.44/0.70      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.44/0.70  thf('20', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.70          | ~ (v1_xboole_0 @ X0)
% 0.44/0.70          | ~ (r2_hidden @ X0 @ sk_B)
% 0.44/0.70          | ~ (v13_waybel_0 @ sk_B @ 
% 0.44/0.70               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.44/0.70          | ~ (v2_waybel_0 @ sk_B @ 
% 0.44/0.70               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.44/0.70          | ~ (v1_subset_1 @ sk_B @ 
% 0.44/0.70               (u1_struct_0 @ 
% 0.44/0.70                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.44/0.70          | (v1_xboole_0 @ sk_B))),
% 0.44/0.70      inference('sup-', [status(thm)], ['13', '19'])).
% 0.44/0.70  thf('21', plain,
% 0.44/0.70      (![X32 : $i]:
% 0.44/0.70         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.44/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.70  thf('22', plain,
% 0.44/0.70      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('23', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('24', plain,
% 0.44/0.70      ((v13_waybel_0 @ sk_B @ 
% 0.44/0.70        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.44/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.70  thf('25', plain,
% 0.44/0.70      (((v13_waybel_0 @ sk_B @ 
% 0.44/0.70         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.44/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.70      inference('sup+', [status(thm)], ['21', '24'])).
% 0.44/0.70  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('27', plain,
% 0.44/0.70      ((v13_waybel_0 @ sk_B @ 
% 0.44/0.70        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.44/0.70  thf('28', plain,
% 0.44/0.70      (![X32 : $i]:
% 0.44/0.70         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.44/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.70  thf('29', plain,
% 0.44/0.70      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('30', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('31', plain,
% 0.44/0.70      ((v2_waybel_0 @ sk_B @ 
% 0.44/0.70        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.44/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.44/0.70  thf('32', plain,
% 0.44/0.70      (((v2_waybel_0 @ sk_B @ 
% 0.44/0.70         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.44/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.70      inference('sup+', [status(thm)], ['28', '31'])).
% 0.44/0.70  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('34', plain,
% 0.44/0.70      ((v2_waybel_0 @ sk_B @ 
% 0.44/0.70        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.70      inference('demod', [status(thm)], ['32', '33'])).
% 0.44/0.70  thf('35', plain,
% 0.44/0.70      (![X32 : $i]:
% 0.44/0.70         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.44/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.70  thf('36', plain,
% 0.44/0.70      ((v1_subset_1 @ sk_B @ 
% 0.44/0.70        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('37', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('38', plain,
% 0.44/0.70      ((v1_subset_1 @ sk_B @ 
% 0.44/0.70        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.44/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.70  thf('39', plain,
% 0.44/0.70      (((v1_subset_1 @ sk_B @ 
% 0.44/0.70         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.44/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.70      inference('sup+', [status(thm)], ['35', '38'])).
% 0.44/0.70  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('41', plain,
% 0.44/0.70      ((v1_subset_1 @ sk_B @ 
% 0.44/0.70        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.70      inference('demod', [status(thm)], ['39', '40'])).
% 0.44/0.70  thf('42', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.70          | ~ (v1_xboole_0 @ X0)
% 0.44/0.70          | ~ (r2_hidden @ X0 @ sk_B)
% 0.44/0.70          | (v1_xboole_0 @ sk_B))),
% 0.44/0.70      inference('demod', [status(thm)], ['20', '27', '34', '41'])).
% 0.44/0.70  thf('43', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ X0 @ sk_B)
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | ~ (v1_xboole_0 @ (sk_C @ sk_B @ X0))
% 0.44/0.70          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['6', '42'])).
% 0.44/0.70  thf('44', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         (~ (v1_xboole_0 @ X0)
% 0.44/0.70          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.44/0.70          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B))),
% 0.44/0.70      inference('sup-', [status(thm)], ['5', '43'])).
% 0.44/0.70  thf('45', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((v1_xboole_0 @ sk_B)
% 0.44/0.70          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.70          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.44/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.70      inference('simplify', [status(thm)], ['44'])).
% 0.44/0.70  thf(fc2_struct_0, axiom,
% 0.44/0.70    (![A:$i]:
% 0.44/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.44/0.70       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.70  thf('46', plain,
% 0.44/0.70      (![X33 : $i]:
% 0.44/0.70         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.44/0.70          | ~ (l1_struct_0 @ X33)
% 0.44/0.70          | (v2_struct_0 @ X33))),
% 0.44/0.70      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.44/0.70  thf('47', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         (~ (v1_xboole_0 @ X0)
% 0.44/0.70          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | (v2_struct_0 @ sk_A)
% 0.44/0.70          | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.70  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('49', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         (~ (v1_xboole_0 @ X0)
% 0.44/0.70          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | (v2_struct_0 @ sk_A))),
% 0.44/0.70      inference('demod', [status(thm)], ['47', '48'])).
% 0.44/0.70  thf('50', plain,
% 0.44/0.70      (![X6 : $i, X7 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.70  thf('51', plain,
% 0.44/0.70      (![X6 : $i, X7 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.70  thf('52', plain,
% 0.44/0.70      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.44/0.70         (~ (r2_hidden @ X8 @ X6)
% 0.44/0.70          | ~ (r2_hidden @ X8 @ X9)
% 0.44/0.70          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.70  thf('53', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ X1 @ X0)
% 0.44/0.70          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.44/0.70          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.44/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.70  thf('54', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i]:
% 0.44/0.70         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.70          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.44/0.70          | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.70      inference('sup-', [status(thm)], ['50', '53'])).
% 0.44/0.70  thf('55', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i]:
% 0.44/0.70         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.70      inference('simplify', [status(thm)], ['54'])).
% 0.44/0.70  thf('56', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((v2_struct_0 @ sk_A)
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | ~ (v1_xboole_0 @ X0)
% 0.44/0.70          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['49', '55'])).
% 0.44/0.70  thf(d5_xboole_0, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i]:
% 0.44/0.70     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.44/0.70       ( ![D:$i]:
% 0.44/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.70           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.44/0.70  thf('57', plain,
% 0.44/0.70      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.44/0.70         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.44/0.70          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.44/0.70          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.44/0.70      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.44/0.70  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.44/0.70  thf('58', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.44/0.70      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.70  thf('59', plain,
% 0.44/0.70      (![X25 : $i, X26 : $i]:
% 0.44/0.70         (~ (r1_xboole_0 @ (k1_tarski @ X25) @ X26) | ~ (r2_hidden @ X25 @ X26))),
% 0.44/0.70      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.44/0.70  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.44/0.70  thf('61', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i]:
% 0.44/0.70         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.44/0.70          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['57', '60'])).
% 0.44/0.70  thf(t4_boole, axiom,
% 0.44/0.70    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.44/0.70  thf('62', plain,
% 0.44/0.70      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 0.44/0.70      inference('cnf', [status(esa)], [t4_boole])).
% 0.44/0.70  thf('63', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i]:
% 0.44/0.70         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.44/0.70          | ((X1) = (k1_xboole_0)))),
% 0.44/0.70      inference('demod', [status(thm)], ['61', '62'])).
% 0.44/0.70  thf(t4_xboole_0, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.70            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.70  thf('64', plain,
% 0.44/0.70      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.44/0.70         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.44/0.70          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.44/0.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.70  thf('65', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i]:
% 0.44/0.70         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.70      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.70  thf('66', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         (~ (v1_xboole_0 @ X0)
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | (v2_struct_0 @ sk_A)
% 0.44/0.70          | ((k3_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.44/0.70      inference('sup-', [status(thm)], ['56', '65'])).
% 0.44/0.70  thf(t100_xboole_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.70  thf('67', plain,
% 0.44/0.70      (![X14 : $i, X15 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ X14 @ X15)
% 0.44/0.70           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.44/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.70  thf('68', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.44/0.70            = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.44/0.70          | (v2_struct_0 @ sk_A)
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['66', '67'])).
% 0.44/0.70  thf(t3_boole, axiom,
% 0.44/0.70    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.70  thf('69', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.70  thf(t48_xboole_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.70  thf('70', plain,
% 0.44/0.70      (![X19 : $i, X20 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.44/0.70           = (k3_xboole_0 @ X19 @ X20))),
% 0.44/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.70  thf('71', plain,
% 0.44/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['69', '70'])).
% 0.44/0.70  thf('72', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.44/0.70      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.70  thf(t88_xboole_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( r1_xboole_0 @ A @ B ) =>
% 0.44/0.70       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.44/0.70  thf('73', plain,
% 0.44/0.70      (![X23 : $i, X24 : $i]:
% 0.44/0.70         (((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24) = (X23))
% 0.44/0.70          | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.44/0.70      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.44/0.70  thf('74', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.44/0.70      inference('sup-', [status(thm)], ['72', '73'])).
% 0.44/0.70  thf('75', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.70  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.70      inference('demod', [status(thm)], ['74', '75'])).
% 0.44/0.70  thf(t46_xboole_1, axiom,
% 0.44/0.70    (![A:$i,B:$i]:
% 0.44/0.70     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.44/0.70  thf('77', plain,
% 0.44/0.70      (![X17 : $i, X18 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.44/0.70      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.44/0.70  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['76', '77'])).
% 0.44/0.70  thf('79', plain,
% 0.44/0.70      (![X19 : $i, X20 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.44/0.70           = (k3_xboole_0 @ X19 @ X20))),
% 0.44/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.70  thf('80', plain,
% 0.44/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['78', '79'])).
% 0.44/0.70  thf('81', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.70  thf('82', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.44/0.70      inference('demod', [status(thm)], ['80', '81'])).
% 0.44/0.70  thf('83', plain,
% 0.44/0.70      (![X14 : $i, X15 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ X14 @ X15)
% 0.44/0.70           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.44/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.70  thf('84', plain,
% 0.44/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['82', '83'])).
% 0.44/0.70  thf('85', plain,
% 0.44/0.70      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.70      inference('demod', [status(thm)], ['71', '84'])).
% 0.44/0.70  thf('86', plain,
% 0.44/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['82', '83'])).
% 0.44/0.70  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['76', '77'])).
% 0.44/0.70  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['86', '87'])).
% 0.44/0.70  thf('89', plain,
% 0.44/0.70      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['85', '88'])).
% 0.44/0.70  thf('90', plain,
% 0.44/0.70      (![X14 : $i, X15 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ X14 @ X15)
% 0.44/0.70           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.44/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.70  thf('91', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['89', '90'])).
% 0.44/0.70  thf('92', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.44/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.70  thf('93', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['91', '92'])).
% 0.44/0.70  thf('94', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (sk_B))
% 0.44/0.70          | (v2_struct_0 @ sk_A)
% 0.44/0.70          | (v1_xboole_0 @ sk_B)
% 0.44/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.70      inference('demod', [status(thm)], ['68', '93'])).
% 0.44/0.70  thf('95', plain,
% 0.44/0.70      (((sk_B)
% 0.44/0.70         != (k2_yellow19 @ sk_A @ 
% 0.44/0.70             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('96', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_B @ 
% 0.44/0.70        (k1_zfmisc_1 @ 
% 0.44/0.70         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.44/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.44/0.70  thf(t14_yellow19, axiom,
% 0.44/0.70    (![A:$i]:
% 0.44/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.44/0.70       ( ![B:$i]:
% 0.44/0.70         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.70             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.70             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.70             ( m1_subset_1 @
% 0.44/0.70               B @ 
% 0.44/0.70               ( k1_zfmisc_1 @
% 0.44/0.70                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.44/0.70           ( ( k7_subset_1 @
% 0.44/0.70               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.44/0.70               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.44/0.70             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.44/0.70  thf('97', plain,
% 0.44/0.70      (![X35 : $i, X36 : $i]:
% 0.44/0.70         ((v1_xboole_0 @ X35)
% 0.44/0.70          | ~ (v2_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.44/0.70          | ~ (v13_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.44/0.70          | ~ (m1_subset_1 @ X35 @ 
% 0.44/0.70               (k1_zfmisc_1 @ 
% 0.44/0.70                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))))
% 0.44/0.70          | ((k7_subset_1 @ 
% 0.44/0.70              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X36))) @ X35 @ 
% 0.44/0.70              (k1_tarski @ k1_xboole_0))
% 0.44/0.70              = (k2_yellow19 @ X36 @ 
% 0.44/0.70                 (k3_yellow19 @ X36 @ (k2_struct_0 @ X36) @ X35)))
% 0.44/0.70          | ~ (l1_struct_0 @ X36)
% 0.44/0.70          | (v2_struct_0 @ X36))),
% 0.44/0.70      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.44/0.70  thf('98', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('99', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('100', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('101', plain,
% 0.44/0.70      (![X34 : $i]: ((k3_yellow_1 @ X34) = (k3_lattice3 @ (k1_lattice3 @ X34)))),
% 0.44/0.70      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.44/0.70  thf('102', plain,
% 0.44/0.70      (![X35 : $i, X36 : $i]:
% 0.44/0.70         ((v1_xboole_0 @ X35)
% 0.44/0.70          | ~ (v2_waybel_0 @ X35 @ 
% 0.44/0.70               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X36))))
% 0.44/0.70          | ~ (v13_waybel_0 @ X35 @ 
% 0.44/0.70               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X36))))
% 0.44/0.70          | ~ (m1_subset_1 @ X35 @ 
% 0.44/0.70               (k1_zfmisc_1 @ 
% 0.44/0.70                (u1_struct_0 @ 
% 0.44/0.70                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X36))))))
% 0.44/0.70          | ((k7_subset_1 @ 
% 0.44/0.70              (u1_struct_0 @ 
% 0.44/0.70               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X36)))) @ 
% 0.44/0.70              X35 @ (k1_tarski @ k1_xboole_0))
% 0.44/0.70              = (k2_yellow19 @ X36 @ 
% 0.44/0.70                 (k3_yellow19 @ X36 @ (k2_struct_0 @ X36) @ X35)))
% 0.44/0.70          | ~ (l1_struct_0 @ X36)
% 0.44/0.70          | (v2_struct_0 @ X36))),
% 0.44/0.70      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.44/0.70  thf('103', plain,
% 0.44/0.70      (((v2_struct_0 @ sk_A)
% 0.44/0.70        | ~ (l1_struct_0 @ sk_A)
% 0.44/0.70        | ((k7_subset_1 @ 
% 0.44/0.70            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.44/0.70            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.44/0.70            = (k2_yellow19 @ sk_A @ 
% 0.44/0.70               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.44/0.70        | ~ (v13_waybel_0 @ sk_B @ 
% 0.44/0.70             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.44/0.70        | ~ (v2_waybel_0 @ sk_B @ 
% 0.44/0.70             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.44/0.70        | (v1_xboole_0 @ sk_B))),
% 0.44/0.70      inference('sup-', [status(thm)], ['96', '102'])).
% 0.44/0.70  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('105', plain,
% 0.44/0.70      ((m1_subset_1 @ sk_B @ 
% 0.44/0.70        (k1_zfmisc_1 @ 
% 0.44/0.70         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.44/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.44/0.70  thf(redefinition_k7_subset_1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i]:
% 0.44/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.70       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.44/0.70  thf('106', plain,
% 0.44/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.70         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.44/0.70          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k4_xboole_0 @ X29 @ X31)))),
% 0.44/0.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.44/0.70  thf('107', plain,
% 0.44/0.70      (![X0 : $i]:
% 0.44/0.70         ((k7_subset_1 @ 
% 0.44/0.70           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.44/0.70           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.70      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.70  thf('108', plain,
% 0.44/0.70      ((v13_waybel_0 @ sk_B @ 
% 0.44/0.70        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.44/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.70  thf('109', plain,
% 0.44/0.70      ((v2_waybel_0 @ sk_B @ 
% 0.44/0.70        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.44/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.44/0.70  thf('110', plain,
% 0.44/0.70      (((v2_struct_0 @ sk_A)
% 0.44/0.70        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.44/0.70            = (k2_yellow19 @ sk_A @ 
% 0.44/0.70               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.44/0.70        | (v1_xboole_0 @ sk_B))),
% 0.44/0.70      inference('demod', [status(thm)], ['103', '104', '107', '108', '109'])).
% 0.44/0.70  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('112', plain,
% 0.44/0.70      (((v1_xboole_0 @ sk_B)
% 0.44/0.70        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.44/0.70            = (k2_yellow19 @ sk_A @ 
% 0.44/0.70               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.70      inference('clc', [status(thm)], ['110', '111'])).
% 0.44/0.70  thf('113', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('114', plain,
% 0.44/0.70      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.44/0.70         = (k2_yellow19 @ sk_A @ 
% 0.44/0.70            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.44/0.70      inference('clc', [status(thm)], ['112', '113'])).
% 0.44/0.70  thf('115', plain,
% 0.44/0.70      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.44/0.70      inference('demod', [status(thm)], ['95', '114'])).
% 0.44/0.70  thf('116', plain,
% 0.44/0.70      ((((sk_B) != (sk_B))
% 0.44/0.70        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.70        | (v1_xboole_0 @ sk_B)
% 0.44/0.70        | (v2_struct_0 @ sk_A))),
% 0.44/0.70      inference('sup-', [status(thm)], ['94', '115'])).
% 0.44/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.70  thf('117', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.70  thf('118', plain,
% 0.44/0.70      ((((sk_B) != (sk_B)) | (v1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.44/0.70      inference('demod', [status(thm)], ['116', '117'])).
% 0.44/0.70  thf('119', plain, (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.44/0.70      inference('simplify', [status(thm)], ['118'])).
% 0.44/0.70  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf('121', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.70      inference('clc', [status(thm)], ['119', '120'])).
% 0.44/0.70  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 0.44/0.70  
% 0.44/0.70  % SZS output end Refutation
% 0.44/0.70  
% 0.44/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
