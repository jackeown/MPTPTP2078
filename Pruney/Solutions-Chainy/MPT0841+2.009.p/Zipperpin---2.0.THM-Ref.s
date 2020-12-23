%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1D6I8Bf9cD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 172 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  788 (2466 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_E_2 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X23 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X23 @ X21 @ X22 ) @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C_1 ) )
   <= ( ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X31 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X23 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X23 @ X21 @ X22 ) @ X21 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X23 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X23 @ X21 @ X22 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v4_relat_1 @ sk_D_2 @ sk_C_1 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('36',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X31 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','24','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

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

thf('46',plain,(
    ! [X9: $i,X10: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X12
       != ( k9_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X10 )
      | ~ ( r2_hidden @ X15 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( r2_hidden @ X15 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X10 )
      | ( r2_hidden @ X14 @ ( k9_relat_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','42','43','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1D6I8Bf9cD
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:49:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 83 iterations in 0.064s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(t52_relset_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @
% 0.21/0.51                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.51                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.21/0.51                         ( ?[F:$i]:
% 0.21/0.51                           ( ( r2_hidden @ F @ B ) & 
% 0.21/0.51                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.21/0.51                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( m1_subset_1 @
% 0.21/0.51                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.21/0.51                      ( ![E:$i]:
% 0.21/0.51                        ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.51                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.21/0.51                            ( ?[F:$i]:
% 0.21/0.51                              ( ( r2_hidden @ F @ B ) & 
% 0.21/0.51                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.21/0.51                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)
% 0.21/0.51        | (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)) | 
% 0.21/0.51       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X31 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X31 @ sk_C_1)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_E_2) @ sk_D_2)
% 0.21/0.51          | ~ (r2_hidden @ X31 @ sk_B)
% 0.21/0.51          | ~ (r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((![X31 : $i]:
% 0.21/0.51          (~ (m1_subset_1 @ X31 @ sk_C_1)
% 0.21/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_E_2) @ sk_D_2)
% 0.21/0.51           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.21/0.51       ~ ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.51          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0)
% 0.21/0.51           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((r2_hidden @ sk_F @ sk_B)
% 0.21/0.51        | (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.51  thf(t143_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.21/0.51         ( ?[D:$i]:
% 0.21/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.21/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X22 @ (k9_relat_1 @ X23 @ X21))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X23 @ X21 @ X22) @ X22) @ X23)
% 0.21/0.51          | ~ (v1_relat_1 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_D_2)
% 0.21/0.51         | (r2_hidden @ 
% 0.21/0.51            (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2)))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.51          | (v1_relat_1 @ X6)
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_D_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(fc6_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.51  thf('16', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((r2_hidden @ 
% 0.21/0.51         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((![X31 : $i]:
% 0.21/0.51          (~ (m1_subset_1 @ X31 @ sk_C_1)
% 0.21/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_E_2) @ sk_D_2)
% 0.21/0.51           | ~ (r2_hidden @ X31 @ sk_B)))
% 0.21/0.51         <= ((![X31 : $i]:
% 0.21/0.51                (~ (m1_subset_1 @ X31 @ sk_C_1)
% 0.21/0.51                 | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_E_2) @ sk_D_2)
% 0.21/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)
% 0.21/0.51         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C_1)))
% 0.21/0.51         <= ((![X31 : $i]:
% 0.21/0.51                (~ (m1_subset_1 @ X31 @ sk_C_1)
% 0.21/0.51                 | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_E_2) @ sk_D_2)
% 0.21/0.51                 | ~ (r2_hidden @ X31 @ sk_B))) & 
% 0.21/0.51             ((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X22 @ (k9_relat_1 @ X23 @ X21))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X23 @ X21 @ X22) @ X21)
% 0.21/0.51          | ~ (v1_relat_1 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_D_2)
% 0.21/0.51         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X22 @ (k9_relat_1 @ X23 @ X21))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X23 @ X21 @ X22) @ (k1_relat_1 @ X23))
% 0.21/0.51          | ~ (v1_relat_1 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_D_2)
% 0.21/0.51         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ 
% 0.21/0.51            (k1_relat_1 @ sk_D_2))))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ (k1_relat_1 @ sk_D_2)))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X24 @ X25)
% 0.21/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('32', plain, ((v4_relat_1 @ sk_D_2 @ sk_C_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf(d18_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (v4_relat_1 @ X16 @ X17)
% 0.21/0.51          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('36', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ sk_C_1)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C_1))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '38'])).
% 0.21/0.51  thf(t1_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C_1))
% 0.21/0.51         <= (((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (~
% 0.21/0.51       (![X31 : $i]:
% 0.21/0.51          (~ (m1_subset_1 @ X31 @ sk_C_1)
% 0.21/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_E_2) @ sk_D_2)
% 0.21/0.51           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.21/0.51       ~ ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '24', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.21/0.51       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['7'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['7'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf(d13_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i,C:$i]:
% 0.21/0.51         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.21/0.51           ( ![D:$i]:
% 0.21/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51               ( ?[E:$i]:
% 0.21/0.51                 ( ( r2_hidden @ E @ B ) & 
% 0.21/0.51                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (((X12) != (k9_relat_1 @ X10 @ X9))
% 0.21/0.51          | (r2_hidden @ X14 @ X12)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X15 @ X14) @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X15 @ X9)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X15 @ X9)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X15 @ X14) @ X10)
% 0.21/0.51          | (r2_hidden @ X14 @ (k9_relat_1 @ X10 @ X9)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ X0))
% 0.21/0.51           | ~ (r2_hidden @ sk_F @ X0)
% 0.21/0.51           | ~ (v1_relat_1 @ sk_D_2)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '47'])).
% 0.21/0.51  thf('49', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ X0))
% 0.21/0.51           | ~ (r2_hidden @ sk_F @ X0)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 0.21/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.21/0.51             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0)
% 0.21/0.51           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r2_hidden @ sk_E_2 @ 
% 0.21/0.51               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.21/0.51       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)) | 
% 0.21/0.51       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '54'])).
% 0.21/0.51  thf('56', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['1', '3', '42', '43', '55'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
