%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LGbIEIK1qp

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 133 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  705 (1623 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X33: $i] :
      ( ~ ( m1_subset_1 @ X33 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X33 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X33 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
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
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_3 @ X22 @ X20 @ X21 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X33 ) @ sk_C_1 ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X33 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X33 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k10_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_3 @ X22 @ X20 @ X21 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','38'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X33 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['18','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LGbIEIK1qp
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:39 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 234 iterations in 0.099s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.21/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
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
% 0.21/0.55      (![X33 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X33 @ sk_B)
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X33) @ sk_C_1)
% 0.21/0.55          | ~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((![X33 : $i]:
% 0.21/0.55          (~ (m1_subset_1 @ X33 @ sk_B)
% 0.21/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X33) @ sk_C_1))) | 
% 0.21/0.55       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.55         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.21/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)
% 0.21/0.55        | (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.55  thf(t169_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X23 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X23 @ (k2_relat_1 @ X23)) = (k1_relat_1 @ X23))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.55  thf(t166_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.55         ( ?[D:$i]:
% 0.21/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X21 @ (k10_relat_1 @ X22 @ X20))
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X21 @ (sk_D_3 @ X22 @ X20 @ X21)) @ X22)
% 0.21/0.55          | ~ (v1_relat_1 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ X1 @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ 
% 0.21/0.55           (k4_tarski @ X1 @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55         | (r2_hidden @ 
% 0.21/0.55            (k4_tarski @ sk_D_4 @ 
% 0.21/0.55             (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4)) @ 
% 0.21/0.55            sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc1_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( v1_relat_1 @ C ) ))).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.55         ((v1_relat_1 @ X24)
% 0.21/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.55  thf('15', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (((r2_hidden @ 
% 0.21/0.55         (k4_tarski @ sk_D_4 @ 
% 0.21/0.55          (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4)) @ 
% 0.21/0.55         sk_C_1))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      ((![X33 : $i]:
% 0.21/0.55          (~ (m1_subset_1 @ X33 @ sk_B)
% 0.21/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X33) @ sk_C_1)))
% 0.21/0.55         <= ((![X33 : $i]:
% 0.21/0.55                (~ (m1_subset_1 @ X33 @ sk_B)
% 0.21/0.55                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X33) @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      ((~ (m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.21/0.55           sk_B))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.21/0.55             (![X33 : $i]:
% 0.21/0.55                (~ (m1_subset_1 @ X33 @ sk_B)
% 0.21/0.55                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X33) @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X23 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X23 @ (k2_relat_1 @ X23)) = (k1_relat_1 @ X23))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X21 @ (k10_relat_1 @ X22 @ X20))
% 0.21/0.55          | (r2_hidden @ (sk_D_3 @ X22 @ X20 @ X21) @ (k2_relat_1 @ X22))
% 0.21/0.55          | ~ (v1_relat_1 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.21/0.55             (k2_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.21/0.55           (k2_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55         | (r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.21/0.55            (k2_relat_1 @ sk_C_1))))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '23'])).
% 0.21/0.55  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.21/0.55         (k2_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.55         ((v5_relat_1 @ X27 @ X29)
% 0.21/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.55  thf('29', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf(d19_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (v5_relat_1 @ X10 @ X11)
% 0.21/0.55          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.55  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf(t28_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k3_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.55  thf(d4_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.55          | (r2_hidden @ X4 @ X2)
% 0.21/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.55         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)) | (r2_hidden @ X0 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ sk_B))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '38'])).
% 0.21/0.55  thf(t1_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (((m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.21/0.55         sk_B))
% 0.21/0.55         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (~
% 0.21/0.55       (![X33 : $i]:
% 0.21/0.55          (~ (m1_subset_1 @ X33 @ sk_B)
% 0.21/0.55           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X33) @ sk_C_1))) | 
% 0.21/0.55       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)) | 
% 0.21/0.55       ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['5'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1))
% 0.21/0.55         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['5'])).
% 0.21/0.55  thf(d4_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 0.21/0.55          | (r2_hidden @ X12 @ X15)
% 0.21/0.55          | ((X15) != (k1_relat_1 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.55         ((r2_hidden @ X12 @ (k1_relat_1 @ X14))
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14))),
% 0.21/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.55         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.55         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (~ ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)) | 
% 0.21/0.55       ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.55  thf('52', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '51'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
