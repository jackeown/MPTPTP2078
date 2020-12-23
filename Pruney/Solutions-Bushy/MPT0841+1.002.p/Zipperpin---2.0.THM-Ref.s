%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0841+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z60u9BSHXi

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:34 EST 2020

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 319 expanded)
%              Number of leaves         :   27 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          : 1174 (5270 expanded)
%              Number of equality atoms :    8 (  35 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t52_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                        <=> ? [F: $i] :
                              ( ( r2_hidden @ F @ B )
                              & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                              & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
   <= ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X30 @ sk_B_1 )
      | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X30 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B_1 )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
      & ( r2_hidden @ sk_F @ sk_B_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B_1 )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
   <= ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X7
       != ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X5 )
      | ~ ( r2_hidden @ X10 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('16',plain,(
    ! [X4: $i,X5: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X5 )
      | ( r2_hidden @ X9 @ ( k9_relat_1 @ X5 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( ( r2_hidden @ sk_F @ sk_B_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k7_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k9_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X8 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('44',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X21 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('48',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X30 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,
    ( ( ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_C ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('52',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( sk_E_1 @ X8 @ X4 @ X5 ) @ X4 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_B_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B_1 @ sk_D_1 ) @ sk_C )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('60',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( r2_hidden @ sk_F @ sk_C ) )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r2_hidden @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_hidden @ sk_E_2 @ sk_A ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
    | ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('75',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('77',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( sk_B @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('78',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_E_2 ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X30 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','12','28','73','74','75','86'])).


%------------------------------------------------------------------------------
