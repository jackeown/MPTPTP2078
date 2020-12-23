%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IB1vUjvABQ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:48 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 159 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  576 (1221 expanded)
%              Number of equality atoms :   26 (  92 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) )
      = ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['9','10','11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','27'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','43'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('45',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IB1vUjvABQ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.75  % Solved by: fo/fo7.sh
% 0.51/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.75  % done 566 iterations in 0.304s
% 0.51/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.75  % SZS output start Refutation
% 0.51/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.75  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.51/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.75  thf(t2_boole, axiom,
% 0.51/0.75    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.51/0.75  thf('0', plain,
% 0.51/0.75      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.75  thf(t12_setfam_1, axiom,
% 0.51/0.75    (![A:$i,B:$i]:
% 0.51/0.75     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.75  thf('1', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('2', plain,
% 0.51/0.75      (![X8 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.51/0.75      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.75  thf(t51_xboole_1, axiom,
% 0.51/0.75    (![A:$i,B:$i]:
% 0.51/0.75     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.51/0.75       ( A ) ))).
% 0.51/0.75  thf('3', plain,
% 0.51/0.75      (![X13 : $i, X14 : $i]:
% 0.51/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.51/0.75           = (X13))),
% 0.51/0.75      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.51/0.75  thf('4', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('5', plain,
% 0.51/0.75      (![X13 : $i, X14 : $i]:
% 0.51/0.75         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14)) @ 
% 0.51/0.75           (k4_xboole_0 @ X13 @ X14)) = (X13))),
% 0.51/0.75      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.75  thf('6', plain,
% 0.51/0.75      (![X0 : $i]:
% 0.51/0.75         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.51/0.75      inference('sup+', [status(thm)], ['2', '5'])).
% 0.51/0.75  thf(t3_boole, axiom,
% 0.51/0.75    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.75  thf('7', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.51/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.75  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.75      inference('demod', [status(thm)], ['6', '7'])).
% 0.51/0.75  thf(t31_xboole_1, axiom,
% 0.51/0.75    (![A:$i,B:$i,C:$i]:
% 0.51/0.75     ( r1_tarski @
% 0.51/0.75       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.51/0.75       ( k2_xboole_0 @ B @ C ) ))).
% 0.51/0.75  thf('9', plain,
% 0.51/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.75         (r1_tarski @ 
% 0.51/0.75          (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)) @ 
% 0.51/0.75          (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.75      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.51/0.75  thf('10', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('11', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf(t23_xboole_1, axiom,
% 0.51/0.75    (![A:$i,B:$i,C:$i]:
% 0.51/0.75     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.51/0.75       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.51/0.75  thf('12', plain,
% 0.51/0.75      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.75         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 0.51/0.75           = (k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X7)))),
% 0.51/0.75      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.51/0.75  thf('13', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('14', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('15', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('16', plain,
% 0.51/0.75      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))
% 0.51/0.75           = (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6)) @ 
% 0.51/0.75              (k1_setfam_1 @ (k2_tarski @ X5 @ X7))))),
% 0.51/0.75      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.51/0.75  thf('17', plain,
% 0.51/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.75         (r1_tarski @ 
% 0.51/0.75          (k1_setfam_1 @ (k2_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))) @ 
% 0.51/0.75          (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.75      inference('demod', [status(thm)], ['9', '10', '11', '16'])).
% 0.51/0.75  thf('18', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.51/0.75          (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.51/0.75      inference('sup+', [status(thm)], ['8', '17'])).
% 0.51/0.75  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.75      inference('demod', [status(thm)], ['6', '7'])).
% 0.51/0.75  thf('20', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.51/0.75      inference('demod', [status(thm)], ['18', '19'])).
% 0.51/0.75  thf(t25_relat_1, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( v1_relat_1 @ A ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( v1_relat_1 @ B ) =>
% 0.51/0.75           ( ( r1_tarski @ A @ B ) =>
% 0.51/0.75             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.51/0.75               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.51/0.75  thf('21', plain,
% 0.51/0.75      (![X26 : $i, X27 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X26)
% 0.51/0.75          | (r1_tarski @ (k2_relat_1 @ X27) @ (k2_relat_1 @ X26))
% 0.51/0.75          | ~ (r1_tarski @ X27 @ X26)
% 0.51/0.75          | ~ (v1_relat_1 @ X27))),
% 0.51/0.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.51/0.75  thf('22', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.51/0.75          | (r1_tarski @ 
% 0.51/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.51/0.75             (k2_relat_1 @ X0))
% 0.51/0.75          | ~ (v1_relat_1 @ X0))),
% 0.51/0.75      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.75  thf('23', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.51/0.75      inference('demod', [status(thm)], ['18', '19'])).
% 0.51/0.75  thf(t3_subset, axiom,
% 0.51/0.75    (![A:$i,B:$i]:
% 0.51/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.75  thf('24', plain,
% 0.51/0.75      (![X21 : $i, X23 : $i]:
% 0.51/0.75         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.51/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.75  thf('25', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.51/0.75          (k1_zfmisc_1 @ X0))),
% 0.51/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.75  thf(cc2_relat_1, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( v1_relat_1 @ A ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.75  thf('26', plain,
% 0.51/0.75      (![X24 : $i, X25 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.51/0.75          | (v1_relat_1 @ X24)
% 0.51/0.75          | ~ (v1_relat_1 @ X25))),
% 0.51/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.75  thf('27', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X0)
% 0.51/0.75          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.75  thf('28', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X0)
% 0.51/0.75          | (r1_tarski @ 
% 0.51/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.51/0.75             (k2_relat_1 @ X0)))),
% 0.51/0.75      inference('clc', [status(thm)], ['22', '27'])).
% 0.51/0.75  thf(t17_xboole_1, axiom,
% 0.51/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.75  thf('29', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.51/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.51/0.75  thf('30', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('31', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.51/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.75  thf('32', plain,
% 0.51/0.75      (![X26 : $i, X27 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X26)
% 0.51/0.75          | (r1_tarski @ (k2_relat_1 @ X27) @ (k2_relat_1 @ X26))
% 0.51/0.75          | ~ (r1_tarski @ X27 @ X26)
% 0.51/0.75          | ~ (v1_relat_1 @ X27))),
% 0.51/0.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.51/0.75  thf('33', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.51/0.75          | (r1_tarski @ 
% 0.51/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.51/0.75             (k2_relat_1 @ X0))
% 0.51/0.75          | ~ (v1_relat_1 @ X0))),
% 0.51/0.75      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.75  thf('34', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.51/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.75  thf('35', plain,
% 0.51/0.75      (![X21 : $i, X23 : $i]:
% 0.51/0.75         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.51/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.75  thf('36', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.51/0.75          (k1_zfmisc_1 @ X0))),
% 0.51/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.75  thf('37', plain,
% 0.51/0.75      (![X24 : $i, X25 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.51/0.75          | (v1_relat_1 @ X24)
% 0.51/0.75          | ~ (v1_relat_1 @ X25))),
% 0.51/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.75  thf('38', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X0)
% 0.51/0.75          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.75  thf('39', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X0)
% 0.51/0.75          | (r1_tarski @ 
% 0.51/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.51/0.75             (k2_relat_1 @ X0)))),
% 0.51/0.75      inference('clc', [status(thm)], ['33', '38'])).
% 0.51/0.75  thf(t19_xboole_1, axiom,
% 0.51/0.75    (![A:$i,B:$i,C:$i]:
% 0.51/0.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.51/0.75       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.51/0.75  thf('40', plain,
% 0.51/0.75      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.75         (~ (r1_tarski @ X2 @ X3)
% 0.51/0.75          | ~ (r1_tarski @ X2 @ X4)
% 0.51/0.75          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.51/0.75      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.51/0.75  thf('41', plain,
% 0.51/0.75      (![X19 : $i, X20 : $i]:
% 0.51/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.51/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.75  thf('42', plain,
% 0.51/0.75      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.75         (~ (r1_tarski @ X2 @ X3)
% 0.51/0.75          | ~ (r1_tarski @ X2 @ X4)
% 0.51/0.75          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.51/0.75      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.75  thf('43', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X0)
% 0.51/0.75          | (r1_tarski @ 
% 0.51/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.51/0.75             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.51/0.75          | ~ (r1_tarski @ 
% 0.51/0.75               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.51/0.75      inference('sup-', [status(thm)], ['39', '42'])).
% 0.51/0.75  thf('44', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_relat_1 @ X0)
% 0.51/0.75          | (r1_tarski @ 
% 0.51/0.75             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.51/0.75             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.51/0.75          | ~ (v1_relat_1 @ X1))),
% 0.51/0.75      inference('sup-', [status(thm)], ['28', '43'])).
% 0.51/0.75  thf(t27_relat_1, conjecture,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( v1_relat_1 @ A ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( v1_relat_1 @ B ) =>
% 0.51/0.75           ( r1_tarski @
% 0.51/0.75             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.51/0.75             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.51/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.75    (~( ![A:$i]:
% 0.51/0.75        ( ( v1_relat_1 @ A ) =>
% 0.51/0.75          ( ![B:$i]:
% 0.51/0.75            ( ( v1_relat_1 @ B ) =>
% 0.51/0.75              ( r1_tarski @
% 0.51/0.75                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.59/0.75                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.59/0.75    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.59/0.75  thf('45', plain,
% 0.59/0.75      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.59/0.75          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('46', plain,
% 0.59/0.75      (![X19 : $i, X20 : $i]:
% 0.59/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.59/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.75  thf('47', plain,
% 0.59/0.75      (![X19 : $i, X20 : $i]:
% 0.59/0.75         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.59/0.75      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.75  thf('48', plain,
% 0.59/0.75      (~ (r1_tarski @ 
% 0.59/0.75          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.59/0.75          (k1_setfam_1 @ 
% 0.59/0.75           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.59/0.75      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.75  thf('49', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.75      inference('sup-', [status(thm)], ['44', '48'])).
% 0.59/0.75  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('52', plain, ($false),
% 0.59/0.75      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.59/0.75  
% 0.59/0.75  % SZS output end Refutation
% 0.59/0.75  
% 0.59/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
