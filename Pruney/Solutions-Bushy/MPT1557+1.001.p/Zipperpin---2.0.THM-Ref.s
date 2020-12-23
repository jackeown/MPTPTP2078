%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1557+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Wb70MoLld

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:47 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 154 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   26
%              Number of atoms          : 1054 (1951 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(t35_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r2_yellow_0 @ A @ B )
            & ( r2_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i,C: $i] :
            ( ( ( r1_tarski @ B @ C )
              & ( r2_yellow_0 @ A @ B )
              & ( r2_yellow_0 @ A @ C ) )
           => ( r1_orders_2 @ A @ ( k2_yellow_0 @ A @ C ) @ ( k2_yellow_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_yellow_0])).

thf('0',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X6 )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ sk_B @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ sk_B @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ X0 @ sk_B @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ sk_B @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_yellow_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(d10_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_yellow_0 @ A @ B )
           => ( ( C
                = ( k2_yellow_0 @ A @ B ) )
            <=> ( ( r1_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_orders_2 @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k2_yellow_0 @ sk_A @ X1 ) @ X0 @ sk_A ) @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( sk_D_1 @ ( k2_yellow_0 @ sk_A @ X1 ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k2_yellow_0 @ sk_A @ X1 ) @ X0 @ sk_A ) @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( sk_D_1 @ ( k2_yellow_0 @ sk_A @ X1 ) @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( sk_D_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( sk_D_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( sk_D_1 @ ( k2_yellow_0 @ sk_A @ X0 ) @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ X4 @ ( sk_D_1 @ X4 @ X6 @ X5 ) )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( sk_D_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) )
      | ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
       != ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X3 )
      | ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X3 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_xboole_0 @ sk_C ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ sk_B @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k2_yellow_0 @ X1 @ X0 ) @ ( k2_yellow_0 @ X1 @ sk_B ) )
      | ~ ( r2_yellow_0 @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X1 @ sk_B )
      | ( r1_orders_2 @ X1 @ ( k2_yellow_0 @ X1 @ X0 ) @ ( k2_yellow_0 @ X1 @ sk_B ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_orders_2 @ sk_A @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).


%------------------------------------------------------------------------------
