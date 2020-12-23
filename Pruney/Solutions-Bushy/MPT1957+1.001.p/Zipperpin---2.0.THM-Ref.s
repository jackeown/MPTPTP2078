%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1957+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ciYWW3Y3za

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  489 ( 933 expanded)
%              Number of equality atoms :   55 ( 102 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t4_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
        = ( k9_setfam_1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_waybel_7])).

thf('0',plain,(
    ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) )
 != ( k9_setfam_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( k2_yellow_1 @ X1 )
      = ( g1_orders_2 @ X1 @ ( k1_yellow_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( k2_yellow_1 @ X1 )
      = ( g1_orders_2 @ X1 @ ( k1_yellow_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k9_setfam_1 @ X9 )
      = ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k9_setfam_1 @ X9 )
      = ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) ) )
      | ( ( u1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) ) )
        = ( k1_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( k2_yellow_1 @ X1 )
      = ( g1_orders_2 @ X1 @ ( k1_yellow_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k2_yellow_1 @ X1 )
      = ( g1_orders_2 @ X1 @ ( k1_yellow_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( u1_orders_2 @ ( k2_yellow_1 @ X0 ) )
        = ( k1_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( ( u1_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k1_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf(dt_k3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( v1_orders_2 @ ( k3_yellow_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('23',plain,(
    ! [X3: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( u1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      = ( k1_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k9_setfam_1 @ X9 )
      = ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
        = X2 )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( u1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      = ( k1_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_1 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v1_orders_2 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('35',plain,(
    ! [X2: $i] :
      ( v1_orders_2 @ ( k3_yellow_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_1 @ X0 )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X3: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_yellow_1 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
        = X2 ) ) ),
    inference(demod,[status(thm)],['30','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_yellow_1 @ X1 )
       != ( k2_yellow_1 @ X0 ) )
      | ( ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_yellow_1 @ X1 )
       != ( k3_yellow_1 @ X0 ) )
      | ( ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) )
        = ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['40'])).

thf('42',plain,(
    ( k9_setfam_1 @ sk_A )
 != ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).


%------------------------------------------------------------------------------
