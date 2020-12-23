%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PvfYAGftn0

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 240 expanded)
%              Number of leaves         :   29 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  844 (3681 expanded)
%              Number of equality atoms :   19 ( 100 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('16',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ( v1_funct_2 @ X22 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('35',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['44','49','50','51','52'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','55','56'])).

thf('58',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf('59',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('60',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('61',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('62',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['24','26'])).

thf('63',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('64',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('77',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['59','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('81',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('82',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['58','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PvfYAGftn0
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 17:18:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 67 iterations in 0.039s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(t31_funct_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.22/0.52         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.22/0.52           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.22/0.52           ( m1_subset_1 @
% 0.22/0.52             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.22/0.52            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.22/0.52              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.22/0.52              ( m1_subset_1 @
% 0.22/0.52                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 0.22/0.52        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( v1_relat_1 @ C ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         ((v1_relat_1 @ X10)
% 0.22/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.52  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(dt_k2_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X8 : $i]:
% 0.22/0.52         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.22/0.52          | ~ (v1_funct_1 @ X8)
% 0.22/0.52          | ~ (v1_relat_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.22/0.52         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.22/0.52         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '9'])).
% 0.22/0.52  thf(t55_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) =>
% 0.22/0.52         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.22/0.52           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X9 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X9)
% 0.22/0.52          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.22/0.52          | ~ (v1_funct_1 @ X9)
% 0.22/0.52          | ~ (v1_relat_1 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X8 : $i]:
% 0.22/0.52         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.22/0.52          | ~ (v1_funct_1 @ X8)
% 0.22/0.52          | ~ (v1_relat_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X8 : $i]:
% 0.22/0.52         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.22/0.52          | ~ (v1_funct_1 @ X8)
% 0.22/0.52          | ~ (v1_relat_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k1_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X13))
% 0.22/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.22/0.52        (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.22/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '19'])).
% 0.22/0.52  thf(t2_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         ((r2_hidden @ X6 @ X7)
% 0.22/0.52          | (v1_xboole_0 @ X7)
% 0.22/0.52          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52        | (r2_hidden @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf(fc1_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('23', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((r2_hidden @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf(d1_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X3 @ X2)
% 0.22/0.52          | (r1_tarski @ X3 @ X1)
% 0.22/0.52          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.52  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X9 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X9)
% 0.22/0.52          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.22/0.52          | ~ (v1_funct_1 @ X9)
% 0.22/0.52          | ~ (v1_relat_1 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.52  thf(t4_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.52         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.22/0.52           ( m1_subset_1 @
% 0.22/0.52             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.22/0.52          | (v1_funct_2 @ X22 @ (k1_relat_1 @ X22) @ X23)
% 0.22/0.52          | ~ (v1_funct_1 @ X22)
% 0.22/0.52          | ~ (v1_relat_1 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.22/0.52             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52         (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | ~ (v2_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.52  thf('32', plain, ((v2_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('33', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52         (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '35'])).
% 0.22/0.52  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '39'])).
% 0.22/0.52  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('42', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52        (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v2_funct_1 @ sk_C_1))),
% 0.22/0.52      inference('sup+', [status(thm)], ['11', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.52         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.22/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('49', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('50', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('51', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('52', plain, ((v2_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('53', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['44', '49', '50', '51', '52'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.22/0.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('55', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.22/0.52       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 0.22/0.52       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['10', '55', '56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (![X9 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X9)
% 0.22/0.52          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.22/0.52          | ~ (v1_funct_1 @ X9)
% 0.22/0.52          | ~ (v1_relat_1 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (![X8 : $i]:
% 0.22/0.52         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.22/0.52          | ~ (v1_funct_1 @ X8)
% 0.22/0.52          | ~ (v1_relat_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (![X8 : $i]:
% 0.22/0.52         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.22/0.52          | ~ (v1_funct_1 @ X8)
% 0.22/0.52          | ~ (v1_relat_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (![X9 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X9)
% 0.22/0.52          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.22/0.52          | ~ (v1_funct_1 @ X9)
% 0.22/0.52          | ~ (v1_relat_1 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.22/0.52          | (m1_subset_1 @ X22 @ 
% 0.22/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X22) @ X23)))
% 0.22/0.52          | ~ (v1_funct_1 @ X22)
% 0.22/0.52          | ~ (v1_relat_1 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.22/0.52             (k1_zfmisc_1 @ 
% 0.22/0.52              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ 
% 0.22/0.52          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A)))
% 0.22/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | ~ (v2_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['62', '65'])).
% 0.22/0.52  thf('67', plain, ((v2_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ 
% 0.22/0.52          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A)))
% 0.22/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['61', '70'])).
% 0.22/0.52  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.22/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.22/0.52  thf('75', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['60', '74'])).
% 0.22/0.52  thf('76', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('77', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C_1) @ sk_A)))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.52        | ~ (v2_funct_1 @ sk_C_1))),
% 0.22/0.52      inference('sup+', [status(thm)], ['59', '78'])).
% 0.22/0.52  thf('80', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('81', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('82', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('83', plain, ((v2_funct_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.22/0.52  thf('85', plain, ($false), inference('demod', [status(thm)], ['58', '84'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
