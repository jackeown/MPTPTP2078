%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SJHdsi3vxW

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:02 EST 2020

% Result     : Theorem 13.91s
% Output     : Refutation 13.91s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 243 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  621 (1759 expanded)
%              Number of equality atoms :   23 ( 102 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['4','17'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X21 ) ) ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ k1_xboole_0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k3_relat_1 @ X42 ) @ ( k3_relat_1 @ X41 ) )
      | ~ ( r1_tarski @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','33'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('36',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) @ X13 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k3_relat_1 @ X42 ) @ ( k3_relat_1 @ X41 ) )
      | ~ ( r1_tarski @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) @ X13 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('41',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','44'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('47',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('53',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['55','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SJHdsi3vxW
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 13.91/14.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.91/14.10  % Solved by: fo/fo7.sh
% 13.91/14.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.91/14.10  % done 15192 iterations in 13.647s
% 13.91/14.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.91/14.10  % SZS output start Refutation
% 13.91/14.10  thf(sk_A_type, type, sk_A: $i).
% 13.91/14.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.91/14.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.91/14.10  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 13.91/14.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.91/14.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.91/14.10  thf(sk_B_type, type, sk_B: $i).
% 13.91/14.10  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 13.91/14.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.91/14.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.91/14.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.91/14.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 13.91/14.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 13.91/14.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.91/14.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.91/14.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.91/14.10  thf(t3_boole, axiom,
% 13.91/14.10    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 13.91/14.10  thf('0', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 13.91/14.10      inference('cnf', [status(esa)], [t3_boole])).
% 13.91/14.10  thf(t51_xboole_1, axiom,
% 13.91/14.10    (![A:$i,B:$i]:
% 13.91/14.10     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 13.91/14.10       ( A ) ))).
% 13.91/14.10  thf('1', plain,
% 13.91/14.10      (![X23 : $i, X24 : $i]:
% 13.91/14.10         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 13.91/14.10           = (X23))),
% 13.91/14.10      inference('cnf', [status(esa)], [t51_xboole_1])).
% 13.91/14.10  thf(t12_setfam_1, axiom,
% 13.91/14.10    (![A:$i,B:$i]:
% 13.91/14.10     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 13.91/14.10  thf('2', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('3', plain,
% 13.91/14.10      (![X23 : $i, X24 : $i]:
% 13.91/14.10         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X23 @ X24)) @ 
% 13.91/14.10           (k4_xboole_0 @ X23 @ X24)) = (X23))),
% 13.91/14.10      inference('demod', [status(thm)], ['1', '2'])).
% 13.91/14.10  thf('4', plain,
% 13.91/14.10      (![X0 : $i]:
% 13.91/14.10         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) @ X0)
% 13.91/14.10           = (X0))),
% 13.91/14.10      inference('sup+', [status(thm)], ['0', '3'])).
% 13.91/14.10  thf('5', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 13.91/14.10      inference('cnf', [status(esa)], [t3_boole])).
% 13.91/14.10  thf(t79_xboole_1, axiom,
% 13.91/14.10    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 13.91/14.10  thf('6', plain,
% 13.91/14.10      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 13.91/14.10      inference('cnf', [status(esa)], [t79_xboole_1])).
% 13.91/14.10  thf('7', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 13.91/14.10      inference('sup+', [status(thm)], ['5', '6'])).
% 13.91/14.10  thf(d3_tarski, axiom,
% 13.91/14.10    (![A:$i,B:$i]:
% 13.91/14.10     ( ( r1_tarski @ A @ B ) <=>
% 13.91/14.10       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 13.91/14.10  thf('8', plain,
% 13.91/14.10      (![X1 : $i, X3 : $i]:
% 13.91/14.10         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 13.91/14.10      inference('cnf', [status(esa)], [d3_tarski])).
% 13.91/14.10  thf(t4_xboole_0, axiom,
% 13.91/14.10    (![A:$i,B:$i]:
% 13.91/14.10     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 13.91/14.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 13.91/14.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 13.91/14.10            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 13.91/14.10  thf('9', plain,
% 13.91/14.10      (![X4 : $i, X6 : $i, X7 : $i]:
% 13.91/14.10         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 13.91/14.10          | ~ (r1_xboole_0 @ X4 @ X7))),
% 13.91/14.10      inference('cnf', [status(esa)], [t4_xboole_0])).
% 13.91/14.10  thf('10', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('11', plain,
% 13.91/14.10      (![X4 : $i, X6 : $i, X7 : $i]:
% 13.91/14.10         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 13.91/14.10          | ~ (r1_xboole_0 @ X4 @ X7))),
% 13.91/14.10      inference('demod', [status(thm)], ['9', '10'])).
% 13.91/14.10  thf('12', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.91/14.10         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 13.91/14.10          | ~ (r1_xboole_0 @ X1 @ X0))),
% 13.91/14.10      inference('sup-', [status(thm)], ['8', '11'])).
% 13.91/14.10  thf('13', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) @ X1)),
% 13.91/14.10      inference('sup-', [status(thm)], ['7', '12'])).
% 13.91/14.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 13.91/14.10  thf('14', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 13.91/14.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.91/14.10  thf(d10_xboole_0, axiom,
% 13.91/14.10    (![A:$i,B:$i]:
% 13.91/14.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.91/14.10  thf('15', plain,
% 13.91/14.10      (![X8 : $i, X10 : $i]:
% 13.91/14.10         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 13.91/14.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.91/14.10  thf('16', plain,
% 13.91/14.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 13.91/14.10      inference('sup-', [status(thm)], ['14', '15'])).
% 13.91/14.10  thf('17', plain,
% 13.91/14.10      (![X0 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 13.91/14.10      inference('sup-', [status(thm)], ['13', '16'])).
% 13.91/14.10  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 13.91/14.10      inference('demod', [status(thm)], ['4', '17'])).
% 13.91/14.10  thf(t31_xboole_1, axiom,
% 13.91/14.10    (![A:$i,B:$i,C:$i]:
% 13.91/14.10     ( r1_tarski @
% 13.91/14.10       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 13.91/14.10       ( k2_xboole_0 @ B @ C ) ))).
% 13.91/14.10  thf('19', plain,
% 13.91/14.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 13.91/14.10         (r1_tarski @ 
% 13.91/14.10          (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k3_xboole_0 @ X19 @ X21)) @ 
% 13.91/14.10          (k2_xboole_0 @ X20 @ X21))),
% 13.91/14.10      inference('cnf', [status(esa)], [t31_xboole_1])).
% 13.91/14.10  thf('20', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('21', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('22', plain,
% 13.91/14.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 13.91/14.10         (r1_tarski @ 
% 13.91/14.10          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X19 @ X20)) @ 
% 13.91/14.10           (k1_setfam_1 @ (k2_tarski @ X19 @ X21))) @ 
% 13.91/14.10          (k2_xboole_0 @ X20 @ X21))),
% 13.91/14.10      inference('demod', [status(thm)], ['19', '20', '21'])).
% 13.91/14.10  thf('23', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (r1_tarski @ 
% 13.91/14.10          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ k1_xboole_0)) @ 
% 13.91/14.10           (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 13.91/14.10          X0)),
% 13.91/14.10      inference('sup+', [status(thm)], ['18', '22'])).
% 13.91/14.10  thf('24', plain,
% 13.91/14.10      (![X0 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 13.91/14.10      inference('sup-', [status(thm)], ['13', '16'])).
% 13.91/14.10  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 13.91/14.10      inference('demod', [status(thm)], ['4', '17'])).
% 13.91/14.10  thf('26', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 13.91/14.10      inference('demod', [status(thm)], ['23', '24', '25'])).
% 13.91/14.10  thf(t31_relat_1, axiom,
% 13.91/14.10    (![A:$i]:
% 13.91/14.10     ( ( v1_relat_1 @ A ) =>
% 13.91/14.10       ( ![B:$i]:
% 13.91/14.10         ( ( v1_relat_1 @ B ) =>
% 13.91/14.10           ( ( r1_tarski @ A @ B ) =>
% 13.91/14.10             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 13.91/14.10  thf('27', plain,
% 13.91/14.10      (![X41 : $i, X42 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X41)
% 13.91/14.10          | (r1_tarski @ (k3_relat_1 @ X42) @ (k3_relat_1 @ X41))
% 13.91/14.10          | ~ (r1_tarski @ X42 @ X41)
% 13.91/14.10          | ~ (v1_relat_1 @ X42))),
% 13.91/14.10      inference('cnf', [status(esa)], [t31_relat_1])).
% 13.91/14.10  thf('28', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 13.91/14.10          | (r1_tarski @ 
% 13.91/14.10             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 13.91/14.10             (k3_relat_1 @ X0))
% 13.91/14.10          | ~ (v1_relat_1 @ X0))),
% 13.91/14.10      inference('sup-', [status(thm)], ['26', '27'])).
% 13.91/14.10  thf('29', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 13.91/14.10      inference('demod', [status(thm)], ['23', '24', '25'])).
% 13.91/14.10  thf(t3_subset, axiom,
% 13.91/14.10    (![A:$i,B:$i]:
% 13.91/14.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.91/14.10  thf('30', plain,
% 13.91/14.10      (![X36 : $i, X38 : $i]:
% 13.91/14.10         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 13.91/14.10      inference('cnf', [status(esa)], [t3_subset])).
% 13.91/14.10  thf('31', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 13.91/14.10          (k1_zfmisc_1 @ X0))),
% 13.91/14.10      inference('sup-', [status(thm)], ['29', '30'])).
% 13.91/14.10  thf(cc2_relat_1, axiom,
% 13.91/14.10    (![A:$i]:
% 13.91/14.10     ( ( v1_relat_1 @ A ) =>
% 13.91/14.10       ( ![B:$i]:
% 13.91/14.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 13.91/14.10  thf('32', plain,
% 13.91/14.10      (![X39 : $i, X40 : $i]:
% 13.91/14.10         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 13.91/14.10          | (v1_relat_1 @ X39)
% 13.91/14.10          | ~ (v1_relat_1 @ X40))),
% 13.91/14.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.91/14.10  thf('33', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X0)
% 13.91/14.10          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 13.91/14.10      inference('sup-', [status(thm)], ['31', '32'])).
% 13.91/14.10  thf('34', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X0)
% 13.91/14.10          | (r1_tarski @ 
% 13.91/14.10             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 13.91/14.10             (k3_relat_1 @ X0)))),
% 13.91/14.10      inference('clc', [status(thm)], ['28', '33'])).
% 13.91/14.10  thf(t17_xboole_1, axiom,
% 13.91/14.10    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 13.91/14.10  thf('35', plain,
% 13.91/14.10      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 13.91/14.10      inference('cnf', [status(esa)], [t17_xboole_1])).
% 13.91/14.10  thf('36', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('37', plain,
% 13.91/14.10      (![X13 : $i, X14 : $i]:
% 13.91/14.10         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14)) @ X13)),
% 13.91/14.10      inference('demod', [status(thm)], ['35', '36'])).
% 13.91/14.10  thf('38', plain,
% 13.91/14.10      (![X41 : $i, X42 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X41)
% 13.91/14.10          | (r1_tarski @ (k3_relat_1 @ X42) @ (k3_relat_1 @ X41))
% 13.91/14.10          | ~ (r1_tarski @ X42 @ X41)
% 13.91/14.10          | ~ (v1_relat_1 @ X42))),
% 13.91/14.10      inference('cnf', [status(esa)], [t31_relat_1])).
% 13.91/14.10  thf('39', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 13.91/14.10          | (r1_tarski @ 
% 13.91/14.10             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 13.91/14.10             (k3_relat_1 @ X0))
% 13.91/14.10          | ~ (v1_relat_1 @ X0))),
% 13.91/14.10      inference('sup-', [status(thm)], ['37', '38'])).
% 13.91/14.10  thf('40', plain,
% 13.91/14.10      (![X13 : $i, X14 : $i]:
% 13.91/14.10         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14)) @ X13)),
% 13.91/14.10      inference('demod', [status(thm)], ['35', '36'])).
% 13.91/14.10  thf('41', plain,
% 13.91/14.10      (![X36 : $i, X38 : $i]:
% 13.91/14.10         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 13.91/14.10      inference('cnf', [status(esa)], [t3_subset])).
% 13.91/14.10  thf('42', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 13.91/14.10          (k1_zfmisc_1 @ X0))),
% 13.91/14.10      inference('sup-', [status(thm)], ['40', '41'])).
% 13.91/14.10  thf('43', plain,
% 13.91/14.10      (![X39 : $i, X40 : $i]:
% 13.91/14.10         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 13.91/14.10          | (v1_relat_1 @ X39)
% 13.91/14.10          | ~ (v1_relat_1 @ X40))),
% 13.91/14.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.91/14.10  thf('44', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X0)
% 13.91/14.10          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 13.91/14.10      inference('sup-', [status(thm)], ['42', '43'])).
% 13.91/14.10  thf('45', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X0)
% 13.91/14.10          | (r1_tarski @ 
% 13.91/14.10             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 13.91/14.10             (k3_relat_1 @ X0)))),
% 13.91/14.10      inference('clc', [status(thm)], ['39', '44'])).
% 13.91/14.10  thf(t19_xboole_1, axiom,
% 13.91/14.10    (![A:$i,B:$i,C:$i]:
% 13.91/14.10     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 13.91/14.10       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 13.91/14.10  thf('46', plain,
% 13.91/14.10      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.91/14.10         (~ (r1_tarski @ X15 @ X16)
% 13.91/14.10          | ~ (r1_tarski @ X15 @ X17)
% 13.91/14.10          | (r1_tarski @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 13.91/14.10      inference('cnf', [status(esa)], [t19_xboole_1])).
% 13.91/14.10  thf('47', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('48', plain,
% 13.91/14.10      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.91/14.10         (~ (r1_tarski @ X15 @ X16)
% 13.91/14.10          | ~ (r1_tarski @ X15 @ X17)
% 13.91/14.10          | (r1_tarski @ X15 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 13.91/14.10      inference('demod', [status(thm)], ['46', '47'])).
% 13.91/14.10  thf('49', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X0)
% 13.91/14.10          | (r1_tarski @ 
% 13.91/14.10             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 13.91/14.10             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X0) @ X2)))
% 13.91/14.10          | ~ (r1_tarski @ 
% 13.91/14.10               (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 13.91/14.10      inference('sup-', [status(thm)], ['45', '48'])).
% 13.91/14.10  thf('50', plain,
% 13.91/14.10      (![X0 : $i, X1 : $i]:
% 13.91/14.10         (~ (v1_relat_1 @ X0)
% 13.91/14.10          | (r1_tarski @ 
% 13.91/14.10             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 13.91/14.10             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 13.91/14.10          | ~ (v1_relat_1 @ X1))),
% 13.91/14.10      inference('sup-', [status(thm)], ['34', '49'])).
% 13.91/14.10  thf(t34_relat_1, conjecture,
% 13.91/14.10    (![A:$i]:
% 13.91/14.10     ( ( v1_relat_1 @ A ) =>
% 13.91/14.10       ( ![B:$i]:
% 13.91/14.10         ( ( v1_relat_1 @ B ) =>
% 13.91/14.10           ( r1_tarski @
% 13.91/14.10             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 13.91/14.10             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 13.91/14.10  thf(zf_stmt_0, negated_conjecture,
% 13.91/14.10    (~( ![A:$i]:
% 13.91/14.10        ( ( v1_relat_1 @ A ) =>
% 13.91/14.10          ( ![B:$i]:
% 13.91/14.10            ( ( v1_relat_1 @ B ) =>
% 13.91/14.10              ( r1_tarski @
% 13.91/14.10                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 13.91/14.10                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 13.91/14.10    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 13.91/14.10  thf('51', plain,
% 13.91/14.10      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 13.91/14.10          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 13.91/14.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.91/14.10  thf('52', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('53', plain,
% 13.91/14.10      (![X34 : $i, X35 : $i]:
% 13.91/14.10         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 13.91/14.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.91/14.10  thf('54', plain,
% 13.91/14.10      (~ (r1_tarski @ 
% 13.91/14.10          (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 13.91/14.10          (k1_setfam_1 @ 
% 13.91/14.10           (k2_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 13.91/14.10      inference('demod', [status(thm)], ['51', '52', '53'])).
% 13.91/14.10  thf('55', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 13.91/14.10      inference('sup-', [status(thm)], ['50', '54'])).
% 13.91/14.10  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 13.91/14.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.91/14.10  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 13.91/14.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.91/14.10  thf('58', plain, ($false),
% 13.91/14.10      inference('demod', [status(thm)], ['55', '56', '57'])).
% 13.91/14.10  
% 13.91/14.10  % SZS output end Refutation
% 13.91/14.10  
% 13.94/14.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
