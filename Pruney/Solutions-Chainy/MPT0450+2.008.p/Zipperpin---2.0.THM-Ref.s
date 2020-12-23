%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dXPFLfkVQx

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:02 EST 2020

% Result     : Theorem 31.92s
% Output     : Refutation 31.92s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 225 expanded)
%              Number of leaves         :   31 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  609 (1657 expanded)
%              Number of equality atoms :   22 (  90 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
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

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['4','15'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X21 ) ) ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ k1_xboole_0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['4','15'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( r1_tarski @ ( k3_relat_1 @ X41 ) @ ( k3_relat_1 @ X40 ) )
      | ~ ( r1_tarski @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_relat_1 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','31'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) @ X13 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( r1_tarski @ ( k3_relat_1 @ X41 ) @ ( k3_relat_1 @ X40 ) )
      | ~ ( r1_tarski @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) @ X13 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_relat_1 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','42'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('45',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

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

thf('49',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dXPFLfkVQx
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:26:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 31.92/32.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.92/32.18  % Solved by: fo/fo7.sh
% 31.92/32.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.92/32.18  % done 20892 iterations in 31.677s
% 31.92/32.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.92/32.18  % SZS output start Refutation
% 31.92/32.18  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 31.92/32.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 31.92/32.18  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 31.92/32.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.92/32.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 31.92/32.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 31.92/32.18  thf(sk_A_type, type, sk_A: $i).
% 31.92/32.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 31.92/32.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.92/32.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 31.92/32.18  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 31.92/32.18  thf(sk_B_type, type, sk_B: $i).
% 31.92/32.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 31.92/32.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 31.92/32.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 31.92/32.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 31.92/32.18  thf(t3_boole, axiom,
% 31.92/32.18    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 31.92/32.18  thf('0', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 31.92/32.18      inference('cnf', [status(esa)], [t3_boole])).
% 31.92/32.18  thf(t51_xboole_1, axiom,
% 31.92/32.18    (![A:$i,B:$i]:
% 31.92/32.18     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 31.92/32.18       ( A ) ))).
% 31.92/32.18  thf('1', plain,
% 31.92/32.18      (![X23 : $i, X24 : $i]:
% 31.92/32.18         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 31.92/32.18           = (X23))),
% 31.92/32.18      inference('cnf', [status(esa)], [t51_xboole_1])).
% 31.92/32.18  thf(t12_setfam_1, axiom,
% 31.92/32.18    (![A:$i,B:$i]:
% 31.92/32.18     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 31.92/32.18  thf('2', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('3', plain,
% 31.92/32.18      (![X23 : $i, X24 : $i]:
% 31.92/32.18         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X23 @ X24)) @ 
% 31.92/32.18           (k4_xboole_0 @ X23 @ X24)) = (X23))),
% 31.92/32.18      inference('demod', [status(thm)], ['1', '2'])).
% 31.92/32.18  thf('4', plain,
% 31.92/32.18      (![X0 : $i]:
% 31.92/32.18         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) @ X0)
% 31.92/32.18           = (X0))),
% 31.92/32.18      inference('sup+', [status(thm)], ['0', '3'])).
% 31.92/32.18  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 31.92/32.18  thf('5', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 31.92/32.18      inference('cnf', [status(esa)], [t65_xboole_1])).
% 31.92/32.18  thf(d3_tarski, axiom,
% 31.92/32.18    (![A:$i,B:$i]:
% 31.92/32.18     ( ( r1_tarski @ A @ B ) <=>
% 31.92/32.18       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 31.92/32.18  thf('6', plain,
% 31.92/32.18      (![X1 : $i, X3 : $i]:
% 31.92/32.18         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 31.92/32.18      inference('cnf', [status(esa)], [d3_tarski])).
% 31.92/32.18  thf(t4_xboole_0, axiom,
% 31.92/32.18    (![A:$i,B:$i]:
% 31.92/32.18     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 31.92/32.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 31.92/32.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 31.92/32.18            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 31.92/32.18  thf('7', plain,
% 31.92/32.18      (![X4 : $i, X6 : $i, X7 : $i]:
% 31.92/32.18         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 31.92/32.18          | ~ (r1_xboole_0 @ X4 @ X7))),
% 31.92/32.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 31.92/32.18  thf('8', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('9', plain,
% 31.92/32.18      (![X4 : $i, X6 : $i, X7 : $i]:
% 31.92/32.18         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 31.92/32.18          | ~ (r1_xboole_0 @ X4 @ X7))),
% 31.92/32.18      inference('demod', [status(thm)], ['7', '8'])).
% 31.92/32.18  thf('10', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.92/32.18         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 31.92/32.18          | ~ (r1_xboole_0 @ X1 @ X0))),
% 31.92/32.18      inference('sup-', [status(thm)], ['6', '9'])).
% 31.92/32.18  thf('11', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) @ X1)),
% 31.92/32.18      inference('sup-', [status(thm)], ['5', '10'])).
% 31.92/32.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 31.92/32.18  thf('12', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 31.92/32.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 31.92/32.18  thf(d10_xboole_0, axiom,
% 31.92/32.18    (![A:$i,B:$i]:
% 31.92/32.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 31.92/32.18  thf('13', plain,
% 31.92/32.18      (![X8 : $i, X10 : $i]:
% 31.92/32.18         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 31.92/32.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 31.92/32.18  thf('14', plain,
% 31.92/32.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 31.92/32.18      inference('sup-', [status(thm)], ['12', '13'])).
% 31.92/32.18  thf('15', plain,
% 31.92/32.18      (![X0 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 31.92/32.18      inference('sup-', [status(thm)], ['11', '14'])).
% 31.92/32.18  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 31.92/32.18      inference('demod', [status(thm)], ['4', '15'])).
% 31.92/32.18  thf(t31_xboole_1, axiom,
% 31.92/32.18    (![A:$i,B:$i,C:$i]:
% 31.92/32.18     ( r1_tarski @
% 31.92/32.18       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 31.92/32.18       ( k2_xboole_0 @ B @ C ) ))).
% 31.92/32.18  thf('17', plain,
% 31.92/32.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 31.92/32.18         (r1_tarski @ 
% 31.92/32.18          (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k3_xboole_0 @ X19 @ X21)) @ 
% 31.92/32.18          (k2_xboole_0 @ X20 @ X21))),
% 31.92/32.18      inference('cnf', [status(esa)], [t31_xboole_1])).
% 31.92/32.18  thf('18', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('19', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('20', plain,
% 31.92/32.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 31.92/32.18         (r1_tarski @ 
% 31.92/32.18          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X19 @ X20)) @ 
% 31.92/32.18           (k1_setfam_1 @ (k2_tarski @ X19 @ X21))) @ 
% 31.92/32.18          (k2_xboole_0 @ X20 @ X21))),
% 31.92/32.18      inference('demod', [status(thm)], ['17', '18', '19'])).
% 31.92/32.18  thf('21', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (r1_tarski @ 
% 31.92/32.18          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ k1_xboole_0)) @ 
% 31.92/32.18           (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 31.92/32.18          X0)),
% 31.92/32.18      inference('sup+', [status(thm)], ['16', '20'])).
% 31.92/32.18  thf('22', plain,
% 31.92/32.18      (![X0 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 31.92/32.18      inference('sup-', [status(thm)], ['11', '14'])).
% 31.92/32.18  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 31.92/32.18      inference('demod', [status(thm)], ['4', '15'])).
% 31.92/32.18  thf('24', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 31.92/32.18      inference('demod', [status(thm)], ['21', '22', '23'])).
% 31.92/32.18  thf(t31_relat_1, axiom,
% 31.92/32.18    (![A:$i]:
% 31.92/32.18     ( ( v1_relat_1 @ A ) =>
% 31.92/32.18       ( ![B:$i]:
% 31.92/32.18         ( ( v1_relat_1 @ B ) =>
% 31.92/32.18           ( ( r1_tarski @ A @ B ) =>
% 31.92/32.18             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 31.92/32.18  thf('25', plain,
% 31.92/32.18      (![X40 : $i, X41 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X40)
% 31.92/32.18          | (r1_tarski @ (k3_relat_1 @ X41) @ (k3_relat_1 @ X40))
% 31.92/32.18          | ~ (r1_tarski @ X41 @ X40)
% 31.92/32.18          | ~ (v1_relat_1 @ X41))),
% 31.92/32.18      inference('cnf', [status(esa)], [t31_relat_1])).
% 31.92/32.18  thf('26', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 31.92/32.18          | (r1_tarski @ 
% 31.92/32.18             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 31.92/32.18             (k3_relat_1 @ X0))
% 31.92/32.18          | ~ (v1_relat_1 @ X0))),
% 31.92/32.18      inference('sup-', [status(thm)], ['24', '25'])).
% 31.92/32.18  thf('27', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 31.92/32.18      inference('demod', [status(thm)], ['21', '22', '23'])).
% 31.92/32.18  thf(t3_subset, axiom,
% 31.92/32.18    (![A:$i,B:$i]:
% 31.92/32.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 31.92/32.18  thf('28', plain,
% 31.92/32.18      (![X35 : $i, X37 : $i]:
% 31.92/32.18         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 31.92/32.18      inference('cnf', [status(esa)], [t3_subset])).
% 31.92/32.18  thf('29', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 31.92/32.18          (k1_zfmisc_1 @ X0))),
% 31.92/32.18      inference('sup-', [status(thm)], ['27', '28'])).
% 31.92/32.18  thf(cc2_relat_1, axiom,
% 31.92/32.18    (![A:$i]:
% 31.92/32.18     ( ( v1_relat_1 @ A ) =>
% 31.92/32.18       ( ![B:$i]:
% 31.92/32.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 31.92/32.18  thf('30', plain,
% 31.92/32.18      (![X38 : $i, X39 : $i]:
% 31.92/32.18         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 31.92/32.18          | (v1_relat_1 @ X38)
% 31.92/32.18          | ~ (v1_relat_1 @ X39))),
% 31.92/32.18      inference('cnf', [status(esa)], [cc2_relat_1])).
% 31.92/32.18  thf('31', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X0)
% 31.92/32.18          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 31.92/32.18      inference('sup-', [status(thm)], ['29', '30'])).
% 31.92/32.18  thf('32', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X0)
% 31.92/32.18          | (r1_tarski @ 
% 31.92/32.18             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 31.92/32.18             (k3_relat_1 @ X0)))),
% 31.92/32.18      inference('clc', [status(thm)], ['26', '31'])).
% 31.92/32.18  thf(t17_xboole_1, axiom,
% 31.92/32.18    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 31.92/32.18  thf('33', plain,
% 31.92/32.18      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 31.92/32.18      inference('cnf', [status(esa)], [t17_xboole_1])).
% 31.92/32.18  thf('34', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('35', plain,
% 31.92/32.18      (![X13 : $i, X14 : $i]:
% 31.92/32.18         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14)) @ X13)),
% 31.92/32.18      inference('demod', [status(thm)], ['33', '34'])).
% 31.92/32.18  thf('36', plain,
% 31.92/32.18      (![X40 : $i, X41 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X40)
% 31.92/32.18          | (r1_tarski @ (k3_relat_1 @ X41) @ (k3_relat_1 @ X40))
% 31.92/32.18          | ~ (r1_tarski @ X41 @ X40)
% 31.92/32.18          | ~ (v1_relat_1 @ X41))),
% 31.92/32.18      inference('cnf', [status(esa)], [t31_relat_1])).
% 31.92/32.18  thf('37', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 31.92/32.18          | (r1_tarski @ 
% 31.92/32.18             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 31.92/32.18             (k3_relat_1 @ X0))
% 31.92/32.18          | ~ (v1_relat_1 @ X0))),
% 31.92/32.18      inference('sup-', [status(thm)], ['35', '36'])).
% 31.92/32.18  thf('38', plain,
% 31.92/32.18      (![X13 : $i, X14 : $i]:
% 31.92/32.18         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14)) @ X13)),
% 31.92/32.18      inference('demod', [status(thm)], ['33', '34'])).
% 31.92/32.18  thf('39', plain,
% 31.92/32.18      (![X35 : $i, X37 : $i]:
% 31.92/32.18         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 31.92/32.18      inference('cnf', [status(esa)], [t3_subset])).
% 31.92/32.18  thf('40', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 31.92/32.18          (k1_zfmisc_1 @ X0))),
% 31.92/32.18      inference('sup-', [status(thm)], ['38', '39'])).
% 31.92/32.18  thf('41', plain,
% 31.92/32.18      (![X38 : $i, X39 : $i]:
% 31.92/32.18         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 31.92/32.18          | (v1_relat_1 @ X38)
% 31.92/32.18          | ~ (v1_relat_1 @ X39))),
% 31.92/32.18      inference('cnf', [status(esa)], [cc2_relat_1])).
% 31.92/32.18  thf('42', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X0)
% 31.92/32.18          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 31.92/32.18      inference('sup-', [status(thm)], ['40', '41'])).
% 31.92/32.18  thf('43', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X0)
% 31.92/32.18          | (r1_tarski @ 
% 31.92/32.18             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 31.92/32.18             (k3_relat_1 @ X0)))),
% 31.92/32.18      inference('clc', [status(thm)], ['37', '42'])).
% 31.92/32.18  thf(t19_xboole_1, axiom,
% 31.92/32.18    (![A:$i,B:$i,C:$i]:
% 31.92/32.18     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 31.92/32.18       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 31.92/32.18  thf('44', plain,
% 31.92/32.18      (![X15 : $i, X16 : $i, X17 : $i]:
% 31.92/32.18         (~ (r1_tarski @ X15 @ X16)
% 31.92/32.18          | ~ (r1_tarski @ X15 @ X17)
% 31.92/32.18          | (r1_tarski @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 31.92/32.18      inference('cnf', [status(esa)], [t19_xboole_1])).
% 31.92/32.18  thf('45', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('46', plain,
% 31.92/32.18      (![X15 : $i, X16 : $i, X17 : $i]:
% 31.92/32.18         (~ (r1_tarski @ X15 @ X16)
% 31.92/32.18          | ~ (r1_tarski @ X15 @ X17)
% 31.92/32.18          | (r1_tarski @ X15 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 31.92/32.18      inference('demod', [status(thm)], ['44', '45'])).
% 31.92/32.18  thf('47', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X0)
% 31.92/32.18          | (r1_tarski @ 
% 31.92/32.18             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 31.92/32.18             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X0) @ X2)))
% 31.92/32.18          | ~ (r1_tarski @ 
% 31.92/32.18               (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 31.92/32.18      inference('sup-', [status(thm)], ['43', '46'])).
% 31.92/32.18  thf('48', plain,
% 31.92/32.18      (![X0 : $i, X1 : $i]:
% 31.92/32.18         (~ (v1_relat_1 @ X0)
% 31.92/32.18          | (r1_tarski @ 
% 31.92/32.18             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 31.92/32.18             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 31.92/32.18          | ~ (v1_relat_1 @ X1))),
% 31.92/32.18      inference('sup-', [status(thm)], ['32', '47'])).
% 31.92/32.18  thf(t34_relat_1, conjecture,
% 31.92/32.18    (![A:$i]:
% 31.92/32.18     ( ( v1_relat_1 @ A ) =>
% 31.92/32.18       ( ![B:$i]:
% 31.92/32.18         ( ( v1_relat_1 @ B ) =>
% 31.92/32.18           ( r1_tarski @
% 31.92/32.18             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 31.92/32.18             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 31.92/32.18  thf(zf_stmt_0, negated_conjecture,
% 31.92/32.18    (~( ![A:$i]:
% 31.92/32.18        ( ( v1_relat_1 @ A ) =>
% 31.92/32.18          ( ![B:$i]:
% 31.92/32.18            ( ( v1_relat_1 @ B ) =>
% 31.92/32.18              ( r1_tarski @
% 31.92/32.18                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 31.92/32.18                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 31.92/32.18    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 31.92/32.18  thf('49', plain,
% 31.92/32.18      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 31.92/32.18          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 31.92/32.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.92/32.18  thf('50', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('51', plain,
% 31.92/32.18      (![X33 : $i, X34 : $i]:
% 31.92/32.18         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 31.92/32.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.92/32.18  thf('52', plain,
% 31.92/32.18      (~ (r1_tarski @ 
% 31.92/32.18          (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.92/32.18          (k1_setfam_1 @ 
% 31.92/32.18           (k2_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 31.92/32.18      inference('demod', [status(thm)], ['49', '50', '51'])).
% 31.92/32.18  thf('53', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 31.92/32.18      inference('sup-', [status(thm)], ['48', '52'])).
% 31.92/32.18  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 31.92/32.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.92/32.18  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 31.92/32.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.92/32.18  thf('56', plain, ($false),
% 31.92/32.18      inference('demod', [status(thm)], ['53', '54', '55'])).
% 31.92/32.18  
% 31.92/32.18  % SZS output end Refutation
% 31.92/32.18  
% 31.92/32.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
