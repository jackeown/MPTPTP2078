%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1094+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XT3UnKokvy

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:02 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 177 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  372 (1200 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_funct_3_type,type,(
    k7_funct_3: $i > $i > $i )).

thf(k9_funct_3_type,type,(
    k9_funct_3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t29_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
      <=> ( v1_finset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
        <=> ( v1_finset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_finset_1])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t100_funct_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) @ A )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_funct_3])).

thf(fc13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_finset_1 @ X6 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_finset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k7_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_funct_1 @ ( k7_funct_3 @ A @ B ) )
      & ( v1_relat_1 @ ( k7_funct_3 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k7_funct_3 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_3])).

thf(redefinition_k9_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( k9_funct_3 @ A @ B )
      = ( k7_funct_3 @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k9_funct_3 @ X9 @ X10 )
      = ( k7_funct_3 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_funct_3])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k9_funct_3 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X4: $i] :
      ( v1_funct_1 @ ( k7_funct_3 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_3])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k9_funct_3 @ X9 @ X10 )
      = ( k7_funct_3 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_funct_3])).

thf('13',plain,(
    ! [X2: $i,X4: $i] :
      ( v1_funct_1 @ ( k9_funct_3 @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf('15',plain,
    ( ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20'])).

thf('22',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('23',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t26_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
       => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X13: $i] :
      ( ~ ( v1_finset_1 @ ( k1_relat_1 @ X13 ) )
      | ( v1_finset_1 @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_finset_1])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20','29'])).

thf('31',plain,(
    v1_finset_1 @ ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf(fc14_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_finset_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_finset_1 @ X7 )
      | ~ ( v1_finset_1 @ X8 )
      | ( v1_finset_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc14_finset_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc2_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_finset_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_finset_1 @ X0 )
      | ~ ( v1_finset_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_finset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20','29'])).

thf('43',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_finset_1 @ sk_A ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['22','44'])).


%------------------------------------------------------------------------------
