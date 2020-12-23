%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0836+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8dXP0fJR5w

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 168 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  789 (2320 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D_1 @ X4 @ X2 ) ) @ X2 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D_1 @ X4 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

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
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
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

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D_1 @ X4 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_E @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
      & ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('54',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['29','51','52','53','58'])).


%------------------------------------------------------------------------------
