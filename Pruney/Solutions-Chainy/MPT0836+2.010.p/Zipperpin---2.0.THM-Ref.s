%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gWp6PhOKNG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 212 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  922 (2656 expanded)
%              Number of equality atoms :    9 (  23 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_D_2 @ X16 @ X14 @ X15 ) ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) ) @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
      & ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('30',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X14 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_relat_1 @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('48',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('51',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('57',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('59',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('61',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ X0 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_relat_1 @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ X0 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('68',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X27 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['11','44','45','46','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gWp6PhOKNG
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:32:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 103 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(t47_relset_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.54                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.20/0.54                     ( ?[E:$i]:
% 0.20/0.54                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.20/0.54                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54                  ( ![D:$i]:
% 0.20/0.54                    ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.54                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.20/0.54                        ( ?[E:$i]:
% 0.20/0.54                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.20/0.54                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)
% 0.20/0.54        | (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf(d4_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.54           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.20/0.54          | (r2_hidden @ X4 @ X7)
% 0.20/0.54          | ((X7) != (k1_relat_1 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 0.20/0.54          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.54         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.20/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X27 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54          | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1)
% 0.20/0.54          | ~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.20/0.54         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('split', [status(esa)], ['8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.20/0.54       ~ ((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.54  thf(t169_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X17 : $i]:
% 0.20/0.54         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.54  thf(t166_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.54         ( ?[D:$i]:
% 0.20/0.54           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.54             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.54             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X15 @ (sk_D_2 @ X16 @ X14 @ X15)) @ X16)
% 0.20/0.54          | ~ (v1_relat_1 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (k4_tarski @ X1 @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ 
% 0.20/0.54           (k4_tarski @ X1 @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54         | (r2_hidden @ 
% 0.20/0.54            (k4_tarski @ sk_D_3 @ 
% 0.20/0.54             (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3)) @ 
% 0.20/0.54            sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.54          | (v1_relat_1 @ X2)
% 0.20/0.54          | ~ (v1_relat_1 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf(fc6_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (((r2_hidden @ 
% 0.20/0.54         (k4_tarski @ sk_D_3 @ 
% 0.20/0.54          (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3)) @ 
% 0.20/0.54         sk_C_1)) <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((![X27 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1)))
% 0.20/0.54         <= ((![X27 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1))))),
% 0.20/0.54      inference('split', [status(esa)], ['8'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54           sk_B))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)) & 
% 0.20/0.54             (![X27 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.54         ((v5_relat_1 @ X21 @ X23)
% 0.20/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.54  thf('28', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X17 : $i]:
% 0.20/0.54         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 0.20/0.54          | (r2_hidden @ (sk_D_2 @ X16 @ X14 @ X15) @ X14)
% 0.20/0.54          | ~ (v1_relat_1 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | (r2_hidden @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.20/0.54             (k2_relat_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.20/0.54           (k2_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54         | (r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54            (k2_relat_1 @ sk_C_1))))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '33'])).
% 0.20/0.54  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54         (k2_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf(t202_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X18 @ (k2_relat_1 @ X19))
% 0.20/0.54          | (r2_hidden @ X18 @ X20)
% 0.20/0.54          | ~ (v5_relat_1 @ X19 @ X20)
% 0.20/0.54          | ~ (v1_relat_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54           | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.20/0.54           | (r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54              X0)))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.20/0.54           | (r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54              X0)))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ sk_B))
% 0.20/0.54         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '40'])).
% 0.20/0.54  thf(t1_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54         sk_B)) <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (~
% 0.20/0.54       (![X27 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1))) | 
% 0.20/0.54       ~ ((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.20/0.54       ((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      ((![X27 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1))) | 
% 0.20/0.54       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['8'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ 
% 0.20/0.54           (k4_tarski @ X1 @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54         | (r2_hidden @ 
% 0.20/0.54            (k4_tarski @ sk_D_3 @ 
% 0.20/0.54             (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3)) @ 
% 0.20/0.54            sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((r2_hidden @ 
% 0.20/0.54         (k4_tarski @ sk_D_3 @ 
% 0.20/0.54          (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3)) @ 
% 0.20/0.54         sk_C_1))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      ((![X27 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1)))
% 0.20/0.54         <= ((![X27 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1))))),
% 0.20/0.54      inference('split', [status(esa)], ['8'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54           sk_B))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.20/0.54             (![X27 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.20/0.54           (k2_relat_1 @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54         | (r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54            (k2_relat_1 @ sk_C_1))))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54         (k2_relat_1 @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X18 @ (k2_relat_1 @ X19))
% 0.20/0.54          | (r2_hidden @ X18 @ X20)
% 0.20/0.54          | ~ (v5_relat_1 @ X19 @ X20)
% 0.20/0.54          | ~ (v1_relat_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54           | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.20/0.54           | (r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54              X0)))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.54  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.20/0.54           | (r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54              X0)))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ sk_B))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['56', '65'])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.54         sk_B))
% 0.20/0.54         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (~
% 0.20/0.54       (![X27 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.54           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X27) @ sk_C_1))) | 
% 0.20/0.54       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '68'])).
% 0.20/0.54  thf('70', plain, ($false),
% 0.20/0.54      inference('sat_resolution*', [status(thm)],
% 0.20/0.54                ['11', '44', '45', '46', '69'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
