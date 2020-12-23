%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F0E3Gi4F7N

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 137 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  680 (1626 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X30 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X30 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X23: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k10_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_2 @ X22 @ X20 @ X21 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_2 @ ( k2_relat_1 @ sk_C_2 ) @ sk_D_3 ) ) @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_2 @ ( k2_relat_1 @ sk_C_2 ) @ sk_D_3 ) ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X30 ) @ sk_C_2 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X30 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_2 @ ( k2_relat_1 @ sk_C_2 ) @ sk_D_3 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      & ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X30 ) @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k10_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_2 @ ( k2_relat_1 @ sk_C_2 ) @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_2 @ ( k2_relat_1 @ sk_C_2 ) @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_2 @ ( k2_relat_1 @ sk_C_2 ) @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_2 @ ( k2_relat_1 @ sk_C_2 ) @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X30 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['20','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F0E3Gi4F7N
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 115 iterations in 0.114s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.21/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.60  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.60  thf(t47_relset_1, conjecture,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.60           ( ![C:$i]:
% 0.21/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60               ( ![D:$i]:
% 0.21/0.60                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.60                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.60                     ( ?[E:$i]:
% 0.21/0.60                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.60                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i]:
% 0.21/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.60          ( ![B:$i]:
% 0.21/0.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.60              ( ![C:$i]:
% 0.21/0.60                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60                  ( ![D:$i]:
% 0.21/0.60                    ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.60                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.60                        ( ?[E:$i]:
% 0.21/0.60                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.60                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.21/0.60  thf('0', plain,
% 0.21/0.60      (![X30 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.60          | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X30) @ sk_C_2)
% 0.21/0.60          | ~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      ((![X30 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X30) @ sk_C_2))) | 
% 0.21/0.60       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.60      inference('split', [status(esa)], ['0'])).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.60         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.21/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.21/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.21/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_2)
% 0.21/0.60        | (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('split', [status(esa)], ['5'])).
% 0.21/0.60  thf('7', plain,
% 0.21/0.60      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.60  thf(t169_relat_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ A ) =>
% 0.21/0.60       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.60  thf('8', plain,
% 0.21/0.60      (![X23 : $i]:
% 0.21/0.60         (((k10_relat_1 @ X23 @ (k2_relat_1 @ X23)) = (k1_relat_1 @ X23))
% 0.21/0.60          | ~ (v1_relat_1 @ X23))),
% 0.21/0.60      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.60  thf(t166_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ C ) =>
% 0.21/0.60       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.60         ( ?[D:$i]:
% 0.21/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.60             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.60             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X21 @ (k10_relat_1 @ X22 @ X20))
% 0.21/0.60          | (r2_hidden @ (k4_tarski @ X21 @ (sk_D_2 @ X22 @ X20 @ X21)) @ X22)
% 0.21/0.60          | ~ (v1_relat_1 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.60          | ~ (v1_relat_1 @ X0)
% 0.21/0.60          | ~ (v1_relat_1 @ X0)
% 0.21/0.60          | (r2_hidden @ 
% 0.21/0.60             (k4_tarski @ X1 @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((r2_hidden @ 
% 0.21/0.60           (k4_tarski @ X1 @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.21/0.60          | ~ (v1_relat_1 @ X0)
% 0.21/0.60          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (((~ (v1_relat_1 @ sk_C_2)
% 0.21/0.60         | (r2_hidden @ 
% 0.21/0.60            (k4_tarski @ sk_D_3 @ 
% 0.21/0.60             (sk_D_2 @ sk_C_2 @ (k2_relat_1 @ sk_C_2) @ sk_D_3)) @ 
% 0.21/0.60            sk_C_2)))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(cc2_relat_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ A ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (![X6 : $i, X7 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.60          | (v1_relat_1 @ X6)
% 0.21/0.60          | ~ (v1_relat_1 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.21/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.60  thf(fc6_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.21/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.60  thf('17', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      (((r2_hidden @ 
% 0.21/0.60         (k4_tarski @ sk_D_3 @ 
% 0.21/0.60          (sk_D_2 @ sk_C_2 @ (k2_relat_1 @ sk_C_2) @ sk_D_3)) @ 
% 0.21/0.60         sk_C_2))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      ((![X30 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X30) @ sk_C_2)))
% 0.21/0.60         <= ((![X30 : $i]:
% 0.21/0.60                (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X30) @ sk_C_2))))),
% 0.21/0.60      inference('split', [status(esa)], ['0'])).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_2 @ (k2_relat_1 @ sk_C_2) @ sk_D_3) @ 
% 0.21/0.60           sk_B))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) & 
% 0.21/0.60             (![X30 : $i]:
% 0.21/0.60                (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X30) @ sk_C_2))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X23 : $i]:
% 0.21/0.60         (((k10_relat_1 @ X23 @ (k2_relat_1 @ X23)) = (k1_relat_1 @ X23))
% 0.21/0.60          | ~ (v1_relat_1 @ X23))),
% 0.21/0.60      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X21 @ (k10_relat_1 @ X22 @ X20))
% 0.21/0.60          | (r2_hidden @ (sk_D_2 @ X22 @ X20 @ X21) @ X20)
% 0.21/0.60          | ~ (v1_relat_1 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.60          | ~ (v1_relat_1 @ X0)
% 0.21/0.60          | ~ (v1_relat_1 @ X0)
% 0.21/0.60          | (r2_hidden @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.21/0.60             (k2_relat_1 @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((r2_hidden @ (sk_D_2 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.21/0.60           (k2_relat_1 @ X0))
% 0.21/0.60          | ~ (v1_relat_1 @ X0)
% 0.21/0.60          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      (((~ (v1_relat_1 @ sk_C_2)
% 0.21/0.60         | (r2_hidden @ (sk_D_2 @ sk_C_2 @ (k2_relat_1 @ sk_C_2) @ sk_D_3) @ 
% 0.21/0.60            (k2_relat_1 @ sk_C_2))))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.60  thf('27', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.60  thf('28', plain,
% 0.21/0.60      (((r2_hidden @ (sk_D_2 @ sk_C_2 @ (k2_relat_1 @ sk_C_2) @ sk_D_3) @ 
% 0.21/0.60         (k2_relat_1 @ sk_C_2)))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(cc2_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.60         ((v5_relat_1 @ X24 @ X26)
% 0.21/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.60  thf('31', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.60  thf(d19_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ B ) =>
% 0.21/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.60  thf('32', plain,
% 0.21/0.60      (![X8 : $i, X9 : $i]:
% 0.21/0.60         (~ (v5_relat_1 @ X8 @ X9)
% 0.21/0.60          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.21/0.60          | ~ (v1_relat_1 @ X8))),
% 0.21/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.21/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.60  thf('34', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.60  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.21/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.60  thf(d3_tarski, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.60          | (r2_hidden @ X0 @ X2)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (((r2_hidden @ (sk_D_2 @ sk_C_2 @ (k2_relat_1 @ sk_C_2) @ sk_D_3) @ sk_B))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '37'])).
% 0.21/0.60  thf(t1_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.60      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      (((m1_subset_1 @ (sk_D_2 @ sk_C_2 @ (k2_relat_1 @ sk_C_2) @ sk_D_3) @ 
% 0.21/0.60         sk_B))
% 0.21/0.60         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.60  thf('41', plain,
% 0.21/0.60      (~
% 0.21/0.60       (![X30 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X30 @ sk_B)
% 0.21/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X30) @ sk_C_2))) | 
% 0.21/0.60       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.60      inference('demod', [status(thm)], ['20', '40'])).
% 0.21/0.60  thf('42', plain,
% 0.21/0.60      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_2)) | 
% 0.21/0.60       ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.60      inference('split', [status(esa)], ['5'])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_2))
% 0.21/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_2)))),
% 0.21/0.60      inference('split', [status(esa)], ['5'])).
% 0.21/0.60  thf(d4_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.60       ( ![C:$i]:
% 0.21/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.60         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.60          | (r2_hidden @ X10 @ X13)
% 0.21/0.60          | ((X13) != (k1_relat_1 @ X12)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.60         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.21/0.60          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.21/0.60      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.60  thf('46', plain,
% 0.21/0.60      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_2)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.21/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.60  thf('48', plain,
% 0.21/0.60      ((~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 0.21/0.60         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_2)))
% 0.41/0.60         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (~ ((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_2)) | 
% 0.41/0.60       ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['46', '49'])).
% 0.41/0.60  thf('51', plain, ($false),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '50'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
