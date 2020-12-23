%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mGk0UkCt6a

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 153 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  696 (2108 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_E @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k7_relset_1 @ X27 @ X28 @ X29 @ X27 )
        = ( k2_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('18',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_A )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X18 @ X19 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
      | ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
      & ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('37',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('40',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
      | ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('47',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      & ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X30 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['11','33','34','35','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mGk0UkCt6a
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 101 iterations in 0.070s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(t47_relset_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.52                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.52                     ( ?[E:$i]:
% 0.21/0.52                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.52                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.52                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.52                        ( ?[E:$i]:
% 0.21/0.52                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.52                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)
% 0.21/0.52        | (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf(d4_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.21/0.52          | (r2_hidden @ X3 @ X6)
% 0.21/0.52          | ((X6) != (k1_relat_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.21/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X30 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2)
% 0.21/0.52          | ~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('split', [status(esa)], ['8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.52         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 0.21/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf(d5_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.52          | (r2_hidden @ X11 @ X13)
% 0.21/0.52          | ((X13) != (k2_relat_1 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.21/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (((r2_hidden @ sk_E @ (k2_relat_1 @ sk_C_2)))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t38_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.52         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.52         (((k7_relset_1 @ X27 @ X28 @ X29 @ X27)
% 0.21/0.52            = (k2_relset_1 @ X27 @ X28 @ X29))
% 0.21/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.52      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (((k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_A)
% 0.21/0.52         = (k2_relset_1 @ sk_A @ sk_B @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_A) = (k2_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k7_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.52          | (m1_subset_1 @ (k7_relset_1 @ X18 @ X19 @ X17 @ X20) @ 
% 0.21/0.52             (k1_zfmisc_1 @ X19)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 0.21/0.52          (k1_zfmisc_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf(t4_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.21/0.52          | (m1_subset_1 @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X1 @ sk_B)
% 0.21/0.52          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.21/0.52          | (m1_subset_1 @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_E @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((![X30 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2)))
% 0.21/0.52         <= ((![X30 : $i]:
% 0.21/0.52                (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2))))),
% 0.21/0.52      inference('split', [status(esa)], ['8'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)) & 
% 0.21/0.52             (![X30 : $i]:
% 0.21/0.52                (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (~
% 0.21/0.52       (![X30 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2))) | 
% 0.21/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 0.21/0.52       ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((![X30 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2))) | 
% 0.21/0.52       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.52      inference('split', [status(esa)], ['8'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 0.21/0.52         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.52         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X7 @ X6)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.21/0.52          | ((X6) != (k1_relat_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X5 : $i, X7 : $i]:
% 0.21/0.52         ((r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.21/0.52          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X5)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_D_4 @ (sk_D_1 @ sk_D_4 @ sk_C_2)) @ sk_C_2))
% 0.21/0.52         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.21/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((r2_hidden @ (sk_D_1 @ sk_D_4 @ sk_C_2) @ (k2_relat_1 @ sk_C_2)))
% 0.21/0.52         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.21/0.52          | (m1_subset_1 @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((m1_subset_1 @ (sk_D_1 @ sk_D_4 @ sk_C_2) @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (((r2_hidden @ (k4_tarski @ sk_D_4 @ (sk_D_1 @ sk_D_4 @ sk_C_2)) @ sk_C_2))
% 0.21/0.52         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '40'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((![X30 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2)))
% 0.21/0.52         <= ((![X30 : $i]:
% 0.21/0.52                (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2))))),
% 0.21/0.52      inference('split', [status(esa)], ['8'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_4 @ sk_C_2) @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) & 
% 0.21/0.52             (![X30 : $i]:
% 0.21/0.52                (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (~
% 0.21/0.52       (![X30 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X30) @ sk_C_2))) | 
% 0.21/0.52       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['45', '48'])).
% 0.21/0.52  thf('50', plain, ($false),
% 0.21/0.52      inference('sat_resolution*', [status(thm)],
% 0.21/0.52                ['11', '33', '34', '35', '49'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
