%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ibnCAIS7E5

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:41 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 385 expanded)
%              Number of leaves         :   44 ( 146 expanded)
%              Depth                    :   24
%              Number of atoms          : 1119 (3603 expanded)
%              Number of equality atoms :   75 ( 301 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ X19 )
      | ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('31',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['7','51'])).

thf('53',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('55',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

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

thf('57',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) @ X31 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X32 @ ( k3_yellow19 @ X32 @ ( k2_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('58',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) ) @ X31 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X32 @ ( k3_yellow19 @ X32 @ ( k2_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('70',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('73',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['63','64','67','70','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','78'])).

thf('80',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['52','79'])).

thf('81',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

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

thf('83',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_subset_1 @ X33 @ ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) ) )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_yellow_1 @ X34 ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_yellow_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) ) ) )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('84',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('87',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('88',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_subset_1 @ X33 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ) )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('91',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('92',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X30: $i] :
      ( ( k3_yellow_1 @ X30 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('94',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['89','90','91','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','95'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('101',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ibnCAIS7E5
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 747 iterations in 0.266s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.54/0.72  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.54/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.72  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.54/0.72  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.54/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.54/0.72  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.72  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.54/0.72  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.54/0.72  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.54/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.72  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.54/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.72  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.54/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.72  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.54/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.72  thf(t15_yellow19, conjecture,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.54/0.72             ( v1_subset_1 @
% 0.54/0.72               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.54/0.72             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.54/0.72             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.54/0.72             ( m1_subset_1 @
% 0.54/0.72               B @ 
% 0.54/0.72               ( k1_zfmisc_1 @
% 0.54/0.72                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.54/0.72           ( ( B ) =
% 0.54/0.72             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.54/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.72    (~( ![A:$i]:
% 0.54/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.54/0.72          ( ![B:$i]:
% 0.54/0.72            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.54/0.72                ( v1_subset_1 @
% 0.54/0.72                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.54/0.72                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.54/0.72                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.54/0.72                ( m1_subset_1 @
% 0.54/0.72                  B @ 
% 0.54/0.72                  ( k1_zfmisc_1 @
% 0.54/0.72                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.54/0.72              ( ( B ) =
% 0.54/0.72                ( k2_yellow19 @
% 0.54/0.72                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.54/0.72    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.54/0.72  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(l27_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.54/0.72  thf('1', plain,
% 0.54/0.72      (![X18 : $i, X19 : $i]:
% 0.54/0.72         ((r1_xboole_0 @ (k1_tarski @ X18) @ X19) | (r2_hidden @ X18 @ X19))),
% 0.54/0.72      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.54/0.72  thf(d1_xboole_0, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.72  thf('2', plain,
% 0.54/0.72      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.54/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.72  thf('3', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.72  thf(t4_xboole_0, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.72            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.54/0.72  thf('4', plain,
% 0.54/0.72      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.54/0.72          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.54/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.54/0.72  thf('5', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.54/0.72          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.72  thf('6', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['2', '5'])).
% 0.54/0.72  thf('7', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((r2_hidden @ X1 @ X0)
% 0.54/0.72          | (v1_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['1', '6'])).
% 0.54/0.72  thf(t48_xboole_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.72  thf('8', plain,
% 0.54/0.72      (![X15 : $i, X16 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.72           = (k3_xboole_0 @ X15 @ X16))),
% 0.54/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.72  thf(t4_boole, axiom,
% 0.54/0.72    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.72  thf('9', plain,
% 0.54/0.72      (![X17 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.54/0.72      inference('cnf', [status(esa)], [t4_boole])).
% 0.54/0.72  thf('10', plain,
% 0.54/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['8', '9'])).
% 0.54/0.72  thf('11', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.72  thf('12', plain,
% 0.54/0.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.72  thf(t100_xboole_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.72  thf('13', plain,
% 0.54/0.72      (![X9 : $i, X10 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X9 @ X10)
% 0.54/0.72           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.72  thf('14', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.72  thf('15', plain,
% 0.54/0.72      (![X15 : $i, X16 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.72           = (k3_xboole_0 @ X15 @ X16))),
% 0.54/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.72  thf('16', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.54/0.72           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.72  thf('18', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.72  thf('19', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.72  thf(t3_boole, axiom,
% 0.54/0.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.72  thf('20', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.54/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.72  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.72  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['18', '21'])).
% 0.54/0.72  thf('23', plain,
% 0.54/0.72      (![X15 : $i, X16 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.72           = (k3_xboole_0 @ X15 @ X16))),
% 0.54/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.72  thf('24', plain,
% 0.54/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['22', '23'])).
% 0.54/0.72  thf('25', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.54/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.72  thf('26', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.72  thf('27', plain,
% 0.54/0.72      (![X5 : $i, X6 : $i]:
% 0.54/0.72         ((r1_xboole_0 @ X5 @ X6)
% 0.54/0.72          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.54/0.72  thf('28', plain,
% 0.54/0.72      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.54/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.72  thf('29', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.72  thf('30', plain,
% 0.54/0.72      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['26', '29'])).
% 0.54/0.72  thf(t6_mcart_1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.72          ( ![B:$i]:
% 0.54/0.72            ( ~( ( r2_hidden @ B @ A ) & 
% 0.54/0.72                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.54/0.72                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.54/0.72                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.54/0.72                       ( r2_hidden @ G @ B ) ) =>
% 0.54/0.72                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.54/0.72  thf('31', plain,
% 0.54/0.72      (![X23 : $i]:
% 0.54/0.72         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X23) @ X23))),
% 0.54/0.72      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.54/0.72  thf('32', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.54/0.72          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.72  thf('33', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.72  thf('34', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['30', '33'])).
% 0.54/0.72  thf('35', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.72  thf('36', plain,
% 0.54/0.72      (![X9 : $i, X10 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X9 @ X10)
% 0.54/0.72           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.72  thf('37', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['35', '36'])).
% 0.54/0.72  thf('38', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.54/0.72          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['34', '37'])).
% 0.54/0.72  thf('39', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.72  thf('40', plain,
% 0.54/0.72      (![X9 : $i, X10 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X9 @ X10)
% 0.54/0.72           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.72  thf('41', plain,
% 0.54/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['39', '40'])).
% 0.54/0.72  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      (![X0 : $i]: (((k5_xboole_0 @ X0 @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.54/0.72  thf('44', plain,
% 0.54/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['39', '40'])).
% 0.54/0.72  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['18', '21'])).
% 0.54/0.72  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['44', '45'])).
% 0.54/0.72  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.72  thf('48', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.54/0.72      inference('sup+', [status(thm)], ['46', '47'])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.72      inference('sup+', [status(thm)], ['43', '48'])).
% 0.54/0.72  thf('50', plain,
% 0.54/0.72      (![X9 : $i, X10 : $i]:
% 0.54/0.72         ((k4_xboole_0 @ X9 @ X10)
% 0.54/0.72           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.72  thf('51', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.54/0.72          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.54/0.72      inference('sup+', [status(thm)], ['49', '50'])).
% 0.54/0.72  thf('52', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((r2_hidden @ X0 @ X1)
% 0.54/0.72          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['7', '51'])).
% 0.54/0.72  thf('53', plain,
% 0.54/0.72      (((sk_B_2)
% 0.54/0.72         != (k2_yellow19 @ sk_A @ 
% 0.54/0.72             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('54', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_2 @ 
% 0.54/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(d2_yellow_1, axiom,
% 0.54/0.72    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.54/0.72  thf('55', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('56', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_2 @ 
% 0.54/0.72        (k1_zfmisc_1 @ 
% 0.54/0.72         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.54/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.54/0.72  thf(t14_yellow19, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.54/0.72             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.54/0.72             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.54/0.72             ( m1_subset_1 @
% 0.54/0.72               B @ 
% 0.54/0.72               ( k1_zfmisc_1 @
% 0.54/0.72                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.54/0.72           ( ( k7_subset_1 @
% 0.54/0.72               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.54/0.72               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.54/0.72             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.54/0.72  thf('57', plain,
% 0.54/0.72      (![X31 : $i, X32 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X31)
% 0.54/0.72          | ~ (v2_waybel_0 @ X31 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))
% 0.54/0.72          | ~ (v13_waybel_0 @ X31 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))
% 0.54/0.72          | ~ (m1_subset_1 @ X31 @ 
% 0.54/0.72               (k1_zfmisc_1 @ 
% 0.54/0.72                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))))
% 0.54/0.72          | ((k7_subset_1 @ 
% 0.54/0.72              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X32))) @ X31 @ 
% 0.54/0.72              (k1_tarski @ k1_xboole_0))
% 0.54/0.72              = (k2_yellow19 @ X32 @ 
% 0.54/0.72                 (k3_yellow19 @ X32 @ (k2_struct_0 @ X32) @ X31)))
% 0.54/0.72          | ~ (l1_struct_0 @ X32)
% 0.54/0.72          | (v2_struct_0 @ X32))),
% 0.54/0.72      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.54/0.72  thf('58', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('59', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('60', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('61', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('62', plain,
% 0.54/0.72      (![X31 : $i, X32 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X31)
% 0.54/0.72          | ~ (v2_waybel_0 @ X31 @ 
% 0.54/0.72               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))
% 0.54/0.72          | ~ (v13_waybel_0 @ X31 @ 
% 0.54/0.72               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))
% 0.54/0.72          | ~ (m1_subset_1 @ X31 @ 
% 0.54/0.72               (k1_zfmisc_1 @ 
% 0.54/0.72                (u1_struct_0 @ 
% 0.54/0.72                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))))
% 0.54/0.72          | ((k7_subset_1 @ 
% 0.54/0.72              (u1_struct_0 @ 
% 0.54/0.72               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32)))) @ 
% 0.54/0.72              X31 @ (k1_tarski @ k1_xboole_0))
% 0.54/0.72              = (k2_yellow19 @ X32 @ 
% 0.54/0.72                 (k3_yellow19 @ X32 @ (k2_struct_0 @ X32) @ X31)))
% 0.54/0.72          | ~ (l1_struct_0 @ X32)
% 0.54/0.72          | (v2_struct_0 @ X32))),
% 0.54/0.72      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.54/0.72  thf('63', plain,
% 0.54/0.72      (((v2_struct_0 @ sk_A)
% 0.54/0.72        | ~ (l1_struct_0 @ sk_A)
% 0.54/0.72        | ((k7_subset_1 @ 
% 0.54/0.72            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.54/0.72            sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.54/0.72            = (k2_yellow19 @ sk_A @ 
% 0.54/0.72               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.54/0.72        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.54/0.72             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.54/0.72        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.54/0.72             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.54/0.72        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.72      inference('sup-', [status(thm)], ['56', '62'])).
% 0.54/0.72  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('65', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_2 @ 
% 0.54/0.72        (k1_zfmisc_1 @ 
% 0.54/0.72         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.54/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.54/0.72  thf(redefinition_k7_subset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.72       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.54/0.72  thf('66', plain,
% 0.54/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.72         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.54/0.72          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.54/0.72      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.54/0.72  thf('67', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((k7_subset_1 @ 
% 0.54/0.72           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.54/0.72           sk_B_2 @ X0) = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.72  thf('68', plain,
% 0.54/0.72      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('69', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('70', plain,
% 0.54/0.72      ((v13_waybel_0 @ sk_B_2 @ 
% 0.54/0.72        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.54/0.72      inference('demod', [status(thm)], ['68', '69'])).
% 0.54/0.72  thf('71', plain,
% 0.54/0.72      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('72', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('73', plain,
% 0.54/0.72      ((v2_waybel_0 @ sk_B_2 @ 
% 0.54/0.72        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.54/0.72      inference('demod', [status(thm)], ['71', '72'])).
% 0.54/0.72  thf('74', plain,
% 0.54/0.72      (((v2_struct_0 @ sk_A)
% 0.54/0.72        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.54/0.72            = (k2_yellow19 @ sk_A @ 
% 0.54/0.72               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.54/0.72        | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.72      inference('demod', [status(thm)], ['63', '64', '67', '70', '73'])).
% 0.54/0.72  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('76', plain,
% 0.54/0.72      (((v1_xboole_0 @ sk_B_2)
% 0.54/0.72        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.54/0.72            = (k2_yellow19 @ sk_A @ 
% 0.54/0.72               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.54/0.72      inference('clc', [status(thm)], ['74', '75'])).
% 0.54/0.72  thf('77', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('78', plain,
% 0.54/0.72      (((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.54/0.72         = (k2_yellow19 @ sk_A @ 
% 0.54/0.72            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.54/0.72      inference('clc', [status(thm)], ['76', '77'])).
% 0.54/0.72  thf('79', plain,
% 0.54/0.72      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['53', '78'])).
% 0.54/0.72  thf('80', plain,
% 0.54/0.72      ((((sk_B_2) != (sk_B_2)) | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.54/0.72      inference('sup-', [status(thm)], ['52', '79'])).
% 0.54/0.72  thf('81', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.54/0.72      inference('simplify', [status(thm)], ['80'])).
% 0.54/0.72  thf('82', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_2 @ 
% 0.54/0.72        (k1_zfmisc_1 @ 
% 0.54/0.72         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.54/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.54/0.72  thf(t2_yellow19, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.72       ( ![B:$i]:
% 0.54/0.72         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.54/0.72             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.54/0.72             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.54/0.72             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.54/0.72             ( m1_subset_1 @
% 0.54/0.72               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.54/0.72           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.54/0.72  thf('83', plain,
% 0.54/0.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X33)
% 0.54/0.72          | ~ (v1_subset_1 @ X33 @ (u1_struct_0 @ (k3_yellow_1 @ X34)))
% 0.54/0.72          | ~ (v2_waybel_0 @ X33 @ (k3_yellow_1 @ X34))
% 0.54/0.72          | ~ (v13_waybel_0 @ X33 @ (k3_yellow_1 @ X34))
% 0.54/0.72          | ~ (m1_subset_1 @ X33 @ 
% 0.54/0.72               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X34))))
% 0.54/0.72          | ~ (r2_hidden @ X35 @ X33)
% 0.54/0.72          | ~ (v1_xboole_0 @ X35)
% 0.54/0.72          | (v1_xboole_0 @ X34))),
% 0.54/0.72      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.54/0.72  thf('84', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('85', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('86', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('87', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('88', plain,
% 0.54/0.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ X33)
% 0.54/0.72          | ~ (v1_subset_1 @ X33 @ 
% 0.54/0.72               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34))))
% 0.54/0.72          | ~ (v2_waybel_0 @ X33 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.54/0.72          | ~ (v13_waybel_0 @ X33 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.54/0.72          | ~ (m1_subset_1 @ X33 @ 
% 0.54/0.72               (k1_zfmisc_1 @ 
% 0.54/0.72                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))))
% 0.54/0.72          | ~ (r2_hidden @ X35 @ X33)
% 0.54/0.72          | ~ (v1_xboole_0 @ X35)
% 0.54/0.72          | (v1_xboole_0 @ X34))),
% 0.54/0.72      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.54/0.72  thf('89', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.54/0.72          | ~ (v1_xboole_0 @ X0)
% 0.54/0.72          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.54/0.72          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.54/0.72               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.54/0.72          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.54/0.72               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.54/0.72          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.54/0.72               (u1_struct_0 @ 
% 0.54/0.72                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.54/0.72          | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.72      inference('sup-', [status(thm)], ['82', '88'])).
% 0.54/0.72  thf('90', plain,
% 0.54/0.72      ((v13_waybel_0 @ sk_B_2 @ 
% 0.54/0.72        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.54/0.72      inference('demod', [status(thm)], ['68', '69'])).
% 0.54/0.72  thf('91', plain,
% 0.54/0.72      ((v2_waybel_0 @ sk_B_2 @ 
% 0.54/0.72        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.54/0.72      inference('demod', [status(thm)], ['71', '72'])).
% 0.54/0.72  thf('92', plain,
% 0.54/0.72      ((v1_subset_1 @ sk_B_2 @ 
% 0.54/0.72        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('93', plain,
% 0.54/0.72      (![X30 : $i]: ((k3_yellow_1 @ X30) = (k3_lattice3 @ (k1_lattice3 @ X30)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.54/0.72  thf('94', plain,
% 0.54/0.72      ((v1_subset_1 @ sk_B_2 @ 
% 0.54/0.72        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.54/0.72      inference('demod', [status(thm)], ['92', '93'])).
% 0.54/0.72  thf('95', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.54/0.72          | ~ (v1_xboole_0 @ X0)
% 0.54/0.72          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.54/0.72          | (v1_xboole_0 @ sk_B_2))),
% 0.54/0.72      inference('demod', [status(thm)], ['89', '90', '91', '94'])).
% 0.54/0.72  thf('96', plain,
% 0.54/0.72      (((v1_xboole_0 @ sk_B_2)
% 0.54/0.72        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.72        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['81', '95'])).
% 0.54/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.72  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.72  thf('98', plain,
% 0.54/0.72      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['96', '97'])).
% 0.54/0.72  thf('99', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('100', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.54/0.72      inference('clc', [status(thm)], ['98', '99'])).
% 0.54/0.72  thf(fc5_struct_0, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.54/0.72       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.54/0.72  thf('101', plain,
% 0.54/0.72      (![X29 : $i]:
% 0.54/0.72         (~ (v1_xboole_0 @ (k2_struct_0 @ X29))
% 0.54/0.72          | ~ (l1_struct_0 @ X29)
% 0.54/0.72          | (v2_struct_0 @ X29))),
% 0.54/0.72      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.54/0.72  thf('102', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.72  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('104', plain, ((v2_struct_0 @ sk_A)),
% 0.54/0.72      inference('demod', [status(thm)], ['102', '103'])).
% 0.54/0.72  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
