%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dCvsttcdf4

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:54 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 160 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  767 (2229 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t47_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                    <=> ? [E: $i] :
                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                          & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('2',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X19 @ X17 ) ) @ X17 )
      | ( X18
       != ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X19 @ X17 ) ) @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('19',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('21',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('35',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('37',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_E @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
      & ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X15 @ X18 )
      | ( X18
       != ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['29','46','47','48','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dCvsttcdf4
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.38  % Solved by: fo/fo7.sh
% 1.20/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.38  % done 706 iterations in 0.923s
% 1.20/1.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.38  % SZS output start Refutation
% 1.20/1.38  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.20/1.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.20/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.38  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.20/1.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.20/1.38  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.20/1.38  thf(sk_E_type, type, sk_E: $i).
% 1.20/1.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.20/1.38  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.20/1.38  thf(t47_relset_1, conjecture,
% 1.20/1.38    (![A:$i]:
% 1.20/1.38     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.20/1.38       ( ![B:$i]:
% 1.20/1.38         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.20/1.38           ( ![C:$i]:
% 1.20/1.38             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.38               ( ![D:$i]:
% 1.20/1.38                 ( ( m1_subset_1 @ D @ A ) =>
% 1.20/1.38                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 1.20/1.38                     ( ?[E:$i]:
% 1.20/1.38                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 1.20/1.38                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 1.20/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.38    (~( ![A:$i]:
% 1.20/1.38        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.20/1.38          ( ![B:$i]:
% 1.20/1.38            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.20/1.38              ( ![C:$i]:
% 1.20/1.38                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.38                  ( ![D:$i]:
% 1.20/1.38                    ( ( m1_subset_1 @ D @ A ) =>
% 1.20/1.38                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 1.20/1.38                        ( ?[E:$i]:
% 1.20/1.38                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 1.20/1.38                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 1.20/1.38    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 1.20/1.38  thf('0', plain,
% 1.20/1.38      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.38  thf(redefinition_k1_relset_1, axiom,
% 1.20/1.38    (![A:$i,B:$i,C:$i]:
% 1.20/1.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.38       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.20/1.38  thf('1', plain,
% 1.20/1.38      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.38         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 1.20/1.38          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.20/1.38      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.20/1.38  thf('2', plain,
% 1.20/1.38      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.20/1.38      inference('sup-', [status(thm)], ['0', '1'])).
% 1.20/1.38  thf('3', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)
% 1.20/1.38        | (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.20/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.38  thf('4', plain,
% 1.20/1.38      (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('split', [status(esa)], ['3'])).
% 1.20/1.38  thf('5', plain,
% 1.20/1.38      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup+', [status(thm)], ['2', '4'])).
% 1.20/1.38  thf(d4_relat_1, axiom,
% 1.20/1.38    (![A:$i,B:$i]:
% 1.20/1.38     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.20/1.38       ( ![C:$i]:
% 1.20/1.38         ( ( r2_hidden @ C @ B ) <=>
% 1.20/1.38           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.20/1.38  thf('6', plain,
% 1.20/1.38      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.20/1.38         (~ (r2_hidden @ X19 @ X18)
% 1.20/1.38          | (r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X19 @ X17)) @ X17)
% 1.20/1.38          | ((X18) != (k1_relat_1 @ X17)))),
% 1.20/1.38      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.20/1.38  thf('7', plain,
% 1.20/1.38      (![X17 : $i, X19 : $i]:
% 1.20/1.38         ((r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X19 @ X17)) @ X17)
% 1.20/1.38          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X17)))),
% 1.20/1.38      inference('simplify', [status(thm)], ['6'])).
% 1.20/1.38  thf('8', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['5', '7'])).
% 1.20/1.38  thf('9', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['5', '7'])).
% 1.20/1.38  thf('10', plain,
% 1.20/1.38      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.38  thf(t4_subset, axiom,
% 1.20/1.38    (![A:$i,B:$i,C:$i]:
% 1.20/1.38     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.20/1.38       ( m1_subset_1 @ A @ C ) ))).
% 1.20/1.38  thf('11', plain,
% 1.20/1.38      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.20/1.38         (~ (r2_hidden @ X9 @ X10)
% 1.20/1.38          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.20/1.38          | (m1_subset_1 @ X9 @ X11))),
% 1.20/1.38      inference('cnf', [status(esa)], [t4_subset])).
% 1.20/1.38  thf('12', plain,
% 1.20/1.38      (![X0 : $i]:
% 1.20/1.38         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.20/1.38      inference('sup-', [status(thm)], ['10', '11'])).
% 1.20/1.38  thf('13', plain,
% 1.20/1.38      (((m1_subset_1 @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ 
% 1.20/1.38         (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['9', '12'])).
% 1.20/1.38  thf(t2_subset, axiom,
% 1.20/1.38    (![A:$i,B:$i]:
% 1.20/1.38     ( ( m1_subset_1 @ A @ B ) =>
% 1.20/1.38       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.20/1.38  thf('14', plain,
% 1.20/1.38      (![X7 : $i, X8 : $i]:
% 1.20/1.38         ((r2_hidden @ X7 @ X8)
% 1.20/1.38          | (v1_xboole_0 @ X8)
% 1.20/1.38          | ~ (m1_subset_1 @ X7 @ X8))),
% 1.20/1.38      inference('cnf', [status(esa)], [t2_subset])).
% 1.20/1.38  thf('15', plain,
% 1.20/1.38      ((((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38         | (r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ 
% 1.20/1.38            (k2_zfmisc_1 @ sk_A @ sk_B))))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['13', '14'])).
% 1.20/1.38  thf(l54_zfmisc_1, axiom,
% 1.20/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.38     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.20/1.38       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.20/1.38  thf('16', plain,
% 1.20/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.38         ((r2_hidden @ X2 @ X3)
% 1.20/1.38          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.20/1.38      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.20/1.38  thf('17', plain,
% 1.20/1.38      ((((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B)))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['15', '16'])).
% 1.20/1.38  thf(t1_subset, axiom,
% 1.20/1.38    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.20/1.38  thf('18', plain,
% 1.20/1.38      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.20/1.38      inference('cnf', [status(esa)], [t1_subset])).
% 1.20/1.38  thf('19', plain,
% 1.20/1.38      ((((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38         | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B)))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['17', '18'])).
% 1.20/1.38  thf('20', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['5', '7'])).
% 1.20/1.38  thf('21', plain,
% 1.20/1.38      (![X25 : $i]:
% 1.20/1.38         (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1)
% 1.20/1.38          | ~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.20/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.38  thf('22', plain,
% 1.20/1.38      ((![X25 : $i]:
% 1.20/1.38          (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1)))
% 1.20/1.38         <= ((![X25 : $i]:
% 1.20/1.38                (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1))))),
% 1.20/1.38      inference('split', [status(esa)], ['21'])).
% 1.20/1.38  thf('23', plain,
% 1.20/1.38      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 1.20/1.38             (![X25 : $i]:
% 1.20/1.38                (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['20', '22'])).
% 1.20/1.38  thf('24', plain,
% 1.20/1.38      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 1.20/1.38             (![X25 : $i]:
% 1.20/1.38                (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['19', '23'])).
% 1.20/1.38  thf('25', plain,
% 1.20/1.38      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.38  thf(t5_subset, axiom,
% 1.20/1.38    (![A:$i,B:$i,C:$i]:
% 1.20/1.38     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.20/1.38          ( v1_xboole_0 @ C ) ) ))).
% 1.20/1.38  thf('26', plain,
% 1.20/1.38      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.20/1.38         (~ (r2_hidden @ X12 @ X13)
% 1.20/1.38          | ~ (v1_xboole_0 @ X14)
% 1.20/1.38          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.20/1.38      inference('cnf', [status(esa)], [t5_subset])).
% 1.20/1.38  thf('27', plain,
% 1.20/1.38      (![X0 : $i]:
% 1.20/1.38         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.20/1.38      inference('sup-', [status(thm)], ['25', '26'])).
% 1.20/1.38  thf('28', plain,
% 1.20/1.38      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 1.20/1.38             (![X25 : $i]:
% 1.20/1.38                (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['24', '27'])).
% 1.20/1.38  thf('29', plain,
% 1.20/1.38      (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 1.20/1.38       ~
% 1.20/1.38       (![X25 : $i]:
% 1.20/1.38          (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['8', '28'])).
% 1.20/1.38  thf('30', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('split', [status(esa)], ['3'])).
% 1.20/1.38  thf('31', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('split', [status(esa)], ['3'])).
% 1.20/1.38  thf('32', plain,
% 1.20/1.38      (![X0 : $i]:
% 1.20/1.38         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.20/1.38      inference('sup-', [status(thm)], ['10', '11'])).
% 1.20/1.38  thf('33', plain,
% 1.20/1.38      (((m1_subset_1 @ (k4_tarski @ sk_D_2 @ sk_E) @ 
% 1.20/1.38         (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['31', '32'])).
% 1.20/1.38  thf('34', plain,
% 1.20/1.38      (![X7 : $i, X8 : $i]:
% 1.20/1.38         ((r2_hidden @ X7 @ X8)
% 1.20/1.38          | (v1_xboole_0 @ X8)
% 1.20/1.38          | ~ (m1_subset_1 @ X7 @ X8))),
% 1.20/1.38      inference('cnf', [status(esa)], [t2_subset])).
% 1.20/1.38  thf('35', plain,
% 1.20/1.38      ((((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38         | (r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ 
% 1.20/1.38            (k2_zfmisc_1 @ sk_A @ sk_B))))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.38  thf('36', plain,
% 1.20/1.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.38         ((r2_hidden @ X2 @ X3)
% 1.20/1.38          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.20/1.38      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.20/1.38  thf('37', plain,
% 1.20/1.38      ((((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38         | (r2_hidden @ sk_E @ sk_B)))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['35', '36'])).
% 1.20/1.38  thf('38', plain,
% 1.20/1.38      (![X0 : $i]:
% 1.20/1.38         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.20/1.38          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.20/1.38      inference('sup-', [status(thm)], ['25', '26'])).
% 1.20/1.38  thf('39', plain,
% 1.20/1.38      ((![X0 : $i]: ((r2_hidden @ sk_E @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['37', '38'])).
% 1.20/1.38  thf('40', plain,
% 1.20/1.38      (((r2_hidden @ sk_E @ sk_B))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['30', '39'])).
% 1.20/1.38  thf('41', plain,
% 1.20/1.38      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.20/1.38      inference('cnf', [status(esa)], [t1_subset])).
% 1.20/1.38  thf('42', plain,
% 1.20/1.38      (((m1_subset_1 @ sk_E @ sk_B))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['40', '41'])).
% 1.20/1.38  thf('43', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('split', [status(esa)], ['3'])).
% 1.20/1.38  thf('44', plain,
% 1.20/1.38      ((![X25 : $i]:
% 1.20/1.38          (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1)))
% 1.20/1.38         <= ((![X25 : $i]:
% 1.20/1.38                (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1))))),
% 1.20/1.38      inference('split', [status(esa)], ['21'])).
% 1.20/1.38  thf('45', plain,
% 1.20/1.38      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) & 
% 1.20/1.38             (![X25 : $i]:
% 1.20/1.38                (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['43', '44'])).
% 1.20/1.38  thf('46', plain,
% 1.20/1.38      (~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 1.20/1.38       ~
% 1.20/1.38       (![X25 : $i]:
% 1.20/1.38          (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['42', '45'])).
% 1.20/1.38  thf('47', plain,
% 1.20/1.38      (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 1.20/1.38       (![X25 : $i]:
% 1.20/1.38          (~ (m1_subset_1 @ X25 @ sk_B)
% 1.20/1.38           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_1)))),
% 1.20/1.38      inference('split', [status(esa)], ['21'])).
% 1.20/1.38  thf('48', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 1.20/1.38       ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.20/1.38      inference('split', [status(esa)], ['3'])).
% 1.20/1.38  thf('49', plain,
% 1.20/1.38      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('split', [status(esa)], ['3'])).
% 1.20/1.38  thf('50', plain,
% 1.20/1.38      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.20/1.38         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 1.20/1.38          | (r2_hidden @ X15 @ X18)
% 1.20/1.38          | ((X18) != (k1_relat_1 @ X17)))),
% 1.20/1.38      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.20/1.38  thf('51', plain,
% 1.20/1.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.20/1.38         ((r2_hidden @ X15 @ (k1_relat_1 @ X17))
% 1.20/1.38          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17))),
% 1.20/1.38      inference('simplify', [status(thm)], ['50'])).
% 1.20/1.38  thf('52', plain,
% 1.20/1.38      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 1.20/1.38         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['49', '51'])).
% 1.20/1.38  thf('53', plain,
% 1.20/1.38      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.20/1.38      inference('sup-', [status(thm)], ['0', '1'])).
% 1.20/1.38  thf('54', plain,
% 1.20/1.38      ((~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 1.20/1.38         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('split', [status(esa)], ['21'])).
% 1.20/1.38  thf('55', plain,
% 1.20/1.38      ((~ (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 1.20/1.38         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 1.20/1.38      inference('sup-', [status(thm)], ['53', '54'])).
% 1.20/1.38  thf('56', plain,
% 1.20/1.38      (~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 1.20/1.38       ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.20/1.38      inference('sup-', [status(thm)], ['52', '55'])).
% 1.20/1.38  thf('57', plain, ($false),
% 1.20/1.38      inference('sat_resolution*', [status(thm)],
% 1.20/1.38                ['29', '46', '47', '48', '56'])).
% 1.20/1.38  
% 1.20/1.38  % SZS output end Refutation
% 1.20/1.38  
% 1.20/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
