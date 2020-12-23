%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ji4qsWz8Xq

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:52 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 142 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  718 (1664 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('0',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X34 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X34 ) @ sk_C_1 ) )
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k10_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( sk_D_3 @ X26 @ X24 @ X25 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X34 ) @ sk_C_1 ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X34 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X34 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('22',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k10_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( sk_D_3 @ X26 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X34 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['20','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('46',plain,
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

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k1_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ji4qsWz8Xq
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 233 iterations in 0.128s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.40/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.58  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.40/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.58  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(t47_relset_1, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58               ( ![D:$i]:
% 0.40/0.58                 ( ( m1_subset_1 @ D @ A ) =>
% 0.40/0.58                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.40/0.58                     ( ?[E:$i]:
% 0.40/0.58                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.40/0.58                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58              ( ![C:$i]:
% 0.40/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58                  ( ![D:$i]:
% 0.40/0.58                    ( ( m1_subset_1 @ D @ A ) =>
% 0.40/0.58                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.40/0.58                        ( ?[E:$i]:
% 0.40/0.58                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.40/0.58                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (![X34 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X34 @ sk_B)
% 0.40/0.58          | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X34) @ sk_C_1)
% 0.40/0.58          | ~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      ((![X34 : $i]:
% 0.40/0.58          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.40/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X34) @ sk_C_1))) | 
% 0.40/0.58       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.40/0.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)
% 0.40/0.58        | (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('split', [status(esa)], ['5'])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['4', '6'])).
% 0.40/0.58  thf(t169_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X27 : $i]:
% 0.40/0.58         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 0.40/0.58          | ~ (v1_relat_1 @ X27))),
% 0.40/0.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.40/0.58  thf(t166_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ C ) =>
% 0.40/0.58       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.40/0.58         ( ?[D:$i]:
% 0.40/0.58           ( ( r2_hidden @ D @ B ) & 
% 0.40/0.58             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.40/0.58             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X25 @ (k10_relat_1 @ X26 @ X24))
% 0.40/0.58          | (r2_hidden @ (k4_tarski @ X25 @ (sk_D_3 @ X26 @ X24 @ X25)) @ X26)
% 0.40/0.58          | ~ (v1_relat_1 @ X26))),
% 0.40/0.58      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | (r2_hidden @ 
% 0.40/0.58             (k4_tarski @ X1 @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r2_hidden @ 
% 0.40/0.58           (k4_tarski @ X1 @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (((~ (v1_relat_1 @ sk_C_1)
% 0.40/0.58         | (r2_hidden @ 
% 0.40/0.58            (k4_tarski @ sk_D_4 @ 
% 0.40/0.58             (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4)) @ 
% 0.40/0.58            sk_C_1)))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.40/0.58          | (v1_relat_1 @ X10)
% 0.40/0.58          | ~ (v1_relat_1 @ X11))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf(fc6_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.58  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (((r2_hidden @ 
% 0.40/0.58         (k4_tarski @ sk_D_4 @ 
% 0.40/0.58          (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4)) @ 
% 0.40/0.58         sk_C_1))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('demod', [status(thm)], ['12', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      ((![X34 : $i]:
% 0.40/0.58          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.40/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X34) @ sk_C_1)))
% 0.40/0.58         <= ((![X34 : $i]:
% 0.40/0.58                (~ (m1_subset_1 @ X34 @ sk_B)
% 0.40/0.58                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X34) @ sk_C_1))))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      ((~ (m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.40/0.58           sk_B))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.40/0.58             (![X34 : $i]:
% 0.40/0.58                (~ (m1_subset_1 @ X34 @ sk_B)
% 0.40/0.58                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X34) @ sk_C_1))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['4', '6'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X27 : $i]:
% 0.40/0.58         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 0.40/0.58          | ~ (v1_relat_1 @ X27))),
% 0.40/0.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X25 @ (k10_relat_1 @ X26 @ X24))
% 0.40/0.58          | (r2_hidden @ (sk_D_3 @ X26 @ X24 @ X25) @ X24)
% 0.40/0.58          | ~ (v1_relat_1 @ X26))),
% 0.40/0.58      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | (r2_hidden @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.40/0.58             (k2_relat_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r2_hidden @ (sk_D_3 @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.40/0.58           (k2_relat_1 @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (((~ (v1_relat_1 @ sk_C_1)
% 0.40/0.58         | (r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.40/0.58            (k2_relat_1 @ sk_C_1))))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '25'])).
% 0.40/0.58  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.40/0.58         (k2_relat_1 @ sk_C_1)))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.58         ((v5_relat_1 @ X28 @ X30)
% 0.40/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.58  thf('31', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.40/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.58  thf(d19_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (v5_relat_1 @ X12 @ X13)
% 0.40/0.58          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.40/0.58          | ~ (v1_relat_1 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('demod', [status(thm)], ['33', '34'])).
% 0.40/0.58  thf(t28_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (((k3_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.58  thf(d4_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.40/0.58       ( ![D:$i]:
% 0.40/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.40/0.58          | (r2_hidden @ X4 @ X2)
% 0.40/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.40/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)) | (r2_hidden @ X0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['37', '39'])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ sk_B))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '40'])).
% 0.40/0.58  thf(t1_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (((m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.40/0.58         sk_B))
% 0.40/0.58         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (~
% 0.40/0.58       (![X34 : $i]:
% 0.40/0.58          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.40/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X34) @ sk_C_1))) | 
% 0.40/0.58       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.40/0.58      inference('demod', [status(thm)], ['20', '43'])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)) | 
% 0.40/0.58       ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.40/0.58      inference('split', [status(esa)], ['5'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1))
% 0.40/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)))),
% 0.40/0.58      inference('split', [status(esa)], ['5'])).
% 0.40/0.58  thf(d4_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( r2_hidden @ C @ B ) <=>
% 0.40/0.58           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.58         (~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16)
% 0.40/0.58          | (r2_hidden @ X14 @ X17)
% 0.40/0.58          | ((X17) != (k1_relat_1 @ X16)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         ((r2_hidden @ X14 @ (k1_relat_1 @ X16))
% 0.40/0.58          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.40/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.40/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['46', '48'])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      ((~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.40/0.58         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      ((~ (r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_1)))
% 0.40/0.58         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      (~ ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_1)) | 
% 0.40/0.58       ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.58  thf('54', plain, ($false),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['1', '44', '45', '53'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
