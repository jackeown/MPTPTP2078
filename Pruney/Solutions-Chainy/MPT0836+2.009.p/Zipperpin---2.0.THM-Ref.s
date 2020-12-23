%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wGhbnPCrvE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 212 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  697 (2320 expanded)
%              Number of equality atoms :   20 (  37 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X32 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X32 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['12','17'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,
    ( ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) )
        = ( k10_relat_1 @ X21 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k10_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D_2 @ X19 @ X17 @ X18 ) ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X32 ) @ sk_C_1 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X32 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X32 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k10_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D_2 @ X19 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('46',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X32 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('49',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k1_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wGhbnPCrvE
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 136 iterations in 0.113s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(t47_relset_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55               ( ![D:$i]:
% 0.21/0.55                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.55                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.55                     ( ?[E:$i]:
% 0.21/0.55                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.55                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55                  ( ![D:$i]:
% 0.21/0.55                    ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.55                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.55                        ( ?[E:$i]:
% 0.21/0.55                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.55                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X32 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X32 @ sk_B)
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X32) @ sk_C_1)
% 0.21/0.55          | ~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((![X32 : $i]:
% 0.21/0.55          (~ (m1_subset_1 @ X32 @ sk_B)
% 0.21/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X32) @ sk_C_1))) | 
% 0.21/0.55       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.55         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.21/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)
% 0.21/0.55        | (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.55         ((v5_relat_1 @ X26 @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.55  thf('10', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf(d19_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (v5_relat_1 @ X4 @ X5)
% 0.21/0.55          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.21/0.55          | ~ (v1_relat_1 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.21/0.55          | (v1_relat_1 @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf(fc6_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.55  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.55  thf(t79_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.55         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.21/0.55          | ((k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) = (X24))
% 0.21/0.55          | ~ (v1_relat_1 @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55        | ((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)) = (sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('22', plain, (((k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)) = (sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf(t71_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.55  thf('23', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf(t182_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( v1_relat_1 @ B ) =>
% 0.21/0.55           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.55             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X20)
% 0.21/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X21 @ X20))
% 0.21/0.55              = (k10_relat_1 @ X21 @ (k1_relat_1 @ X20)))
% 0.21/0.55          | ~ (v1_relat_1 @ X21))),
% 0.21/0.55      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.55  thf('26', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      ((((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['22', '27'])).
% 0.21/0.55  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('30', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf(t166_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.55         ( ?[D:$i]:
% 0.21/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X18 @ (k10_relat_1 @ X19 @ X17))
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X18 @ (sk_D_2 @ X19 @ X17 @ X18)) @ X19)
% 0.21/0.55          | ~ (v1_relat_1 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.21/0.55          | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ sk_C_1 @ sk_B @ X0)) @ 
% 0.21/0.55             sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ sk_C_1 @ sk_B @ X0)) @ 
% 0.21/0.55             sk_C_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((r2_hidden @ 
% 0.21/0.55         (k4_tarski @ sk_D_3 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3)) @ sk_C_1))
% 0.21/0.55         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      ((![X32 : $i]:
% 0.21/0.55          (~ (m1_subset_1 @ X32 @ sk_B)
% 0.21/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X32) @ sk_C_1)))
% 0.21/0.55         <= ((![X32 : $i]:
% 0.21/0.55                (~ (m1_subset_1 @ X32 @ sk_B)
% 0.21/0.55                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X32) @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.21/0.55         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.21/0.55             (![X32 : $i]:
% 0.21/0.55                (~ (m1_subset_1 @ X32 @ sk_B)
% 0.21/0.55                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X32) @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.55  thf('39', plain, (((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X18 @ (k10_relat_1 @ X19 @ X17))
% 0.21/0.55          | (r2_hidden @ (sk_D_2 @ X19 @ X17 @ X18) @ X17)
% 0.21/0.55          | ~ (v1_relat_1 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.21/0.55          | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.21/0.55          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.21/0.55         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['38', '43'])).
% 0.21/0.55  thf(t1_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.21/0.55         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (~
% 0.21/0.55       (![X32 : $i]:
% 0.21/0.55          (~ (m1_subset_1 @ X32 @ sk_B)
% 0.21/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X32) @ sk_C_1))) | 
% 0.21/0.55       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['37', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)) | 
% 0.21/0.55       ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['5'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1))
% 0.21/0.55         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['5'])).
% 0.21/0.55  thf(d4_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.21/0.55          | (r2_hidden @ X6 @ X9)
% 0.21/0.55          | ((X9) != (k1_relat_1 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         ((r2_hidden @ X6 @ (k1_relat_1 @ X8))
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8))),
% 0.21/0.55      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '51'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.55         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (~ ((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)) | 
% 0.21/0.55       ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '55'])).
% 0.21/0.55  thf('57', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['1', '47', '48', '56'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
