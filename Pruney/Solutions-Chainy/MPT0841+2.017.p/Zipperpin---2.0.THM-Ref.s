%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IiDVJxUB5Z

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:24 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 249 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          : 1218 (3666 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X24 @ X22 ) )
      | ( r2_hidden @ ( sk_D @ X24 @ X22 @ X23 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) )
        = X25 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( r1_tarski @ ( k1_relat_1 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C_1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('32',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X24 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X24 @ X22 @ X23 ) @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
      | ~ ( r2_hidden @ X36 @ sk_B_1 )
      | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
   <= ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X36 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C_1 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X24 @ X22 ) )
      | ( r2_hidden @ ( sk_D @ X24 @ X22 @ X23 ) @ X22 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_B_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C_1 )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X8 )
        = X8 )
      | ~ ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) )
    | ~ ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( m1_subset_1 @ sk_F @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
   <= ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
   <= ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X36 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('65',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B_1 )
      | ~ ( m1_subset_1 @ sk_F @ sk_C_1 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
      & ( r2_hidden @ sk_F @ sk_B_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ~ ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X36 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) )
    | ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X36 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('69',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('70',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
   <= ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('71',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ X23 @ ( k9_relat_1 @ X24 @ X22 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('77',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ X29 )
      | ( r2_hidden @ X27 @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('78',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('80',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( ( r2_hidden @ sk_F @ sk_B_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('84',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('85',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','60','67','68','69','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IiDVJxUB5Z
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.80/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.80/1.98  % Solved by: fo/fo7.sh
% 1.80/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/1.98  % done 760 iterations in 1.526s
% 1.80/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.80/1.98  % SZS output start Refutation
% 1.80/1.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.80/1.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.80/1.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.80/1.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/1.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.80/1.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.80/1.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.80/1.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.80/1.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.80/1.98  thf(sk_B_type, type, sk_B: $i > $i).
% 1.80/1.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.80/1.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.80/1.98  thf(sk_F_type, type, sk_F: $i).
% 1.80/1.98  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.80/1.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.80/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.80/1.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.80/1.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.80/1.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.80/1.98  thf(sk_E_type, type, sk_E: $i).
% 1.80/1.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.80/1.98  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.80/1.98  thf(t52_relset_1, conjecture,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.80/1.98       ( ![B:$i]:
% 1.80/1.98         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.80/1.98           ( ![C:$i]:
% 1.80/1.98             ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.80/1.98               ( ![D:$i]:
% 1.80/1.98                 ( ( m1_subset_1 @
% 1.80/1.98                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.80/1.98                   ( ![E:$i]:
% 1.80/1.98                     ( ( m1_subset_1 @ E @ A ) =>
% 1.80/1.98                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.80/1.98                         ( ?[F:$i]:
% 1.80/1.98                           ( ( r2_hidden @ F @ B ) & 
% 1.80/1.98                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.80/1.98                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.80/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.80/1.98    (~( ![A:$i]:
% 1.80/1.98        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.80/1.98          ( ![B:$i]:
% 1.80/1.98            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.80/1.98              ( ![C:$i]:
% 1.80/1.98                ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.80/1.98                  ( ![D:$i]:
% 1.80/1.98                    ( ( m1_subset_1 @
% 1.80/1.98                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.80/1.98                      ( ![E:$i]:
% 1.80/1.98                        ( ( m1_subset_1 @ E @ A ) =>
% 1.80/1.98                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.80/1.98                            ( ?[F:$i]:
% 1.80/1.98                              ( ( r2_hidden @ F @ B ) & 
% 1.80/1.98                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.80/1.98                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.80/1.98    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 1.80/1.98  thf('0', plain,
% 1.80/1.98      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)
% 1.80/1.98        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('1', plain,
% 1.80/1.98      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 1.80/1.98       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['0'])).
% 1.80/1.98  thf('2', plain,
% 1.80/1.98      (((m1_subset_1 @ sk_F @ sk_C_1)
% 1.80/1.98        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('3', plain,
% 1.80/1.98      (((m1_subset_1 @ sk_F @ sk_C_1)) | 
% 1.80/1.98       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['2'])).
% 1.80/1.98  thf('4', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf(redefinition_k7_relset_1, axiom,
% 1.80/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.80/1.98       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.80/1.98  thf('5', plain,
% 1.80/1.98      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.80/1.98         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.80/1.98          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 1.80/1.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.80/1.98  thf('6', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ X0)
% 1.80/1.98           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['4', '5'])).
% 1.80/1.98  thf('7', plain,
% 1.80/1.98      (((r2_hidden @ sk_F @ sk_B_1)
% 1.80/1.98        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('8', plain,
% 1.80/1.98      (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('split', [status(esa)], ['7'])).
% 1.80/1.98  thf('9', plain,
% 1.80/1.98      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup+', [status(thm)], ['6', '8'])).
% 1.80/1.98  thf(t143_relat_1, axiom,
% 1.80/1.98    (![A:$i,B:$i,C:$i]:
% 1.80/1.98     ( ( v1_relat_1 @ C ) =>
% 1.80/1.98       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.80/1.98         ( ?[D:$i]:
% 1.80/1.98           ( ( r2_hidden @ D @ B ) & 
% 1.80/1.98             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.80/1.98             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.80/1.98  thf('10', plain,
% 1.80/1.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.80/1.98         (~ (r2_hidden @ X23 @ (k9_relat_1 @ X24 @ X22))
% 1.80/1.98          | (r2_hidden @ (sk_D @ X24 @ X22 @ X23) @ (k1_relat_1 @ X24))
% 1.80/1.98          | ~ (v1_relat_1 @ X24))),
% 1.80/1.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.80/1.98  thf('11', plain,
% 1.80/1.98      (((~ (v1_relat_1 @ sk_D_1)
% 1.80/1.98         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['9', '10'])).
% 1.80/1.98  thf('12', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf(cc2_relat_1, axiom,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( v1_relat_1 @ A ) =>
% 1.80/1.98       ( ![B:$i]:
% 1.80/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.80/1.98  thf('13', plain,
% 1.80/1.98      (![X17 : $i, X18 : $i]:
% 1.80/1.98         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.80/1.98          | (v1_relat_1 @ X17)
% 1.80/1.98          | ~ (v1_relat_1 @ X18))),
% 1.80/1.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.80/1.98  thf('14', plain,
% 1.80/1.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_D_1))),
% 1.80/1.98      inference('sup-', [status(thm)], ['12', '13'])).
% 1.80/1.98  thf(fc6_relat_1, axiom,
% 1.80/1.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.80/1.98  thf('15', plain,
% 1.80/1.98      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 1.80/1.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.80/1.98  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 1.80/1.98      inference('demod', [status(thm)], ['14', '15'])).
% 1.80/1.98  thf('17', plain,
% 1.80/1.98      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ (k1_relat_1 @ sk_D_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('demod', [status(thm)], ['11', '16'])).
% 1.80/1.98  thf(t195_relat_1, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.80/1.98          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 1.80/1.98               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 1.80/1.98  thf('18', plain,
% 1.80/1.98      (![X25 : $i, X26 : $i]:
% 1.80/1.98         (((X25) = (k1_xboole_0))
% 1.80/1.98          | ((k1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26)) = (X25))
% 1.80/1.98          | ((X26) = (k1_xboole_0)))),
% 1.80/1.98      inference('cnf', [status(esa)], [t195_relat_1])).
% 1.80/1.98  thf('19', plain,
% 1.80/1.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf(t3_subset, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.80/1.98  thf('20', plain,
% 1.80/1.98      (![X14 : $i, X15 : $i]:
% 1.80/1.98         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.80/1.98      inference('cnf', [status(esa)], [t3_subset])).
% 1.80/1.98  thf('21', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))),
% 1.80/1.98      inference('sup-', [status(thm)], ['19', '20'])).
% 1.80/1.98  thf(t25_relat_1, axiom,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( v1_relat_1 @ A ) =>
% 1.80/1.98       ( ![B:$i]:
% 1.80/1.98         ( ( v1_relat_1 @ B ) =>
% 1.80/1.98           ( ( r1_tarski @ A @ B ) =>
% 1.80/1.98             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.80/1.98               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.80/1.98  thf('22', plain,
% 1.80/1.98      (![X30 : $i, X31 : $i]:
% 1.80/1.98         (~ (v1_relat_1 @ X30)
% 1.80/1.98          | (r1_tarski @ (k1_relat_1 @ X31) @ (k1_relat_1 @ X30))
% 1.80/1.98          | ~ (r1_tarski @ X31 @ X30)
% 1.80/1.98          | ~ (v1_relat_1 @ X31))),
% 1.80/1.98      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.80/1.98  thf('23', plain,
% 1.80/1.98      ((~ (v1_relat_1 @ sk_D_1)
% 1.80/1.98        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ 
% 1.80/1.98           (k1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 1.80/1.98        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['21', '22'])).
% 1.80/1.98  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 1.80/1.98      inference('demod', [status(thm)], ['14', '15'])).
% 1.80/1.98  thf('25', plain,
% 1.80/1.98      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 1.80/1.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.80/1.98  thf('26', plain,
% 1.80/1.98      ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ 
% 1.80/1.98        (k1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.80/1.98      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.80/1.98  thf('27', plain,
% 1.80/1.98      (((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_C_1)
% 1.80/1.98        | ((sk_A) = (k1_xboole_0))
% 1.80/1.98        | ((sk_C_1) = (k1_xboole_0)))),
% 1.80/1.98      inference('sup+', [status(thm)], ['18', '26'])).
% 1.80/1.98  thf(d3_tarski, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( r1_tarski @ A @ B ) <=>
% 1.80/1.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.80/1.98  thf('28', plain,
% 1.80/1.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.80/1.98         (~ (r2_hidden @ X3 @ X4)
% 1.80/1.98          | (r2_hidden @ X3 @ X5)
% 1.80/1.98          | ~ (r1_tarski @ X4 @ X5))),
% 1.80/1.98      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/1.98  thf('29', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         (((sk_C_1) = (k1_xboole_0))
% 1.80/1.98          | ((sk_A) = (k1_xboole_0))
% 1.80/1.98          | (r2_hidden @ X0 @ sk_C_1)
% 1.80/1.98          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['27', '28'])).
% 1.80/1.98  thf('30', plain,
% 1.80/1.98      ((((r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C_1)
% 1.80/1.98         | ((sk_A) = (k1_xboole_0))
% 1.80/1.98         | ((sk_C_1) = (k1_xboole_0))))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['17', '29'])).
% 1.80/1.98  thf(t1_subset, axiom,
% 1.80/1.98    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.80/1.98  thf('31', plain,
% 1.80/1.98      (![X12 : $i, X13 : $i]:
% 1.80/1.98         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 1.80/1.98      inference('cnf', [status(esa)], [t1_subset])).
% 1.80/1.98  thf('32', plain,
% 1.80/1.98      (((((sk_C_1) = (k1_xboole_0))
% 1.80/1.98         | ((sk_A) = (k1_xboole_0))
% 1.80/1.98         | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['30', '31'])).
% 1.80/1.98  thf('33', plain,
% 1.80/1.98      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup+', [status(thm)], ['6', '8'])).
% 1.80/1.98  thf('34', plain,
% 1.80/1.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.80/1.98         (~ (r2_hidden @ X23 @ (k9_relat_1 @ X24 @ X22))
% 1.80/1.98          | (r2_hidden @ (k4_tarski @ (sk_D @ X24 @ X22 @ X23) @ X23) @ X24)
% 1.80/1.98          | ~ (v1_relat_1 @ X24))),
% 1.80/1.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.80/1.98  thf('35', plain,
% 1.80/1.98      (((~ (v1_relat_1 @ sk_D_1)
% 1.80/1.98         | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_E) @ 
% 1.80/1.98            sk_D_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['33', '34'])).
% 1.80/1.98  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 1.80/1.98      inference('demod', [status(thm)], ['14', '15'])).
% 1.80/1.98  thf('37', plain,
% 1.80/1.98      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_E) @ 
% 1.80/1.98         sk_D_1))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('demod', [status(thm)], ['35', '36'])).
% 1.80/1.98  thf('38', plain,
% 1.80/1.98      (![X36 : $i]:
% 1.80/1.98         (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98          | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98          | ~ (r2_hidden @ X36 @ sk_B_1)
% 1.80/1.98          | ~ (r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('39', plain,
% 1.80/1.98      ((![X36 : $i]:
% 1.80/1.98          (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98           | ~ (r2_hidden @ X36 @ sk_B_1)))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))))),
% 1.80/1.98      inference('split', [status(esa)], ['38'])).
% 1.80/1.98  thf('40', plain,
% 1.80/1.98      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_B_1)
% 1.80/1.98         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C_1)))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['37', '39'])).
% 1.80/1.98  thf('41', plain,
% 1.80/1.98      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup+', [status(thm)], ['6', '8'])).
% 1.80/1.98  thf('42', plain,
% 1.80/1.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.80/1.98         (~ (r2_hidden @ X23 @ (k9_relat_1 @ X24 @ X22))
% 1.80/1.98          | (r2_hidden @ (sk_D @ X24 @ X22 @ X23) @ X22)
% 1.80/1.98          | ~ (v1_relat_1 @ X24))),
% 1.80/1.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.80/1.98  thf('43', plain,
% 1.80/1.98      (((~ (v1_relat_1 @ sk_D_1)
% 1.80/1.98         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_B_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['41', '42'])).
% 1.80/1.98  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 1.80/1.98      inference('demod', [status(thm)], ['14', '15'])).
% 1.80/1.98  thf('45', plain,
% 1.80/1.98      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_B_1))
% 1.80/1.98         <= (((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('demod', [status(thm)], ['43', '44'])).
% 1.80/1.98  thf('46', plain,
% 1.80/1.98      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C_1))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('demod', [status(thm)], ['40', '45'])).
% 1.80/1.98  thf('47', plain,
% 1.80/1.98      (((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0))))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['32', '46'])).
% 1.80/1.98  thf('48', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('49', plain,
% 1.80/1.98      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['47', '48'])).
% 1.80/1.98  thf(d1_xboole_0, axiom,
% 1.80/1.98    (![A:$i]:
% 1.80/1.98     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.80/1.98  thf('50', plain,
% 1.80/1.98      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.80/1.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.80/1.98  thf(l22_zfmisc_1, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( r2_hidden @ A @ B ) =>
% 1.80/1.98       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 1.80/1.98  thf('51', plain,
% 1.80/1.98      (![X8 : $i, X9 : $i]:
% 1.80/1.98         (((k2_xboole_0 @ (k1_tarski @ X9) @ X8) = (X8))
% 1.80/1.98          | ~ (r2_hidden @ X9 @ X8))),
% 1.80/1.98      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 1.80/1.98  thf('52', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((v1_xboole_0 @ X0)
% 1.80/1.98          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['50', '51'])).
% 1.80/1.98  thf(t49_zfmisc_1, axiom,
% 1.80/1.98    (![A:$i,B:$i]:
% 1.80/1.98     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.80/1.98  thf('53', plain,
% 1.80/1.98      (![X10 : $i, X11 : $i]:
% 1.80/1.98         ((k2_xboole_0 @ (k1_tarski @ X10) @ X11) != (k1_xboole_0))),
% 1.80/1.98      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.80/1.98  thf('54', plain,
% 1.80/1.98      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['52', '53'])).
% 1.80/1.98  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.80/1.98      inference('simplify', [status(thm)], ['54'])).
% 1.80/1.98  thf('56', plain,
% 1.80/1.98      ((((sk_A) = (k1_xboole_0)))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('demod', [status(thm)], ['49', '55'])).
% 1.80/1.98  thf('57', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.80/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.98  thf('58', plain,
% 1.80/1.98      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['56', '57'])).
% 1.80/1.98  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.80/1.98      inference('simplify', [status(thm)], ['54'])).
% 1.80/1.98  thf('60', plain,
% 1.80/1.98      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))) | 
% 1.80/1.98       ~
% 1.80/1.98       (![X36 : $i]:
% 1.80/1.98          (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98           | ~ (r2_hidden @ X36 @ sk_B_1)))),
% 1.80/1.98      inference('demod', [status(thm)], ['58', '59'])).
% 1.80/1.98  thf('61', plain,
% 1.80/1.98      (((m1_subset_1 @ sk_F @ sk_C_1)) <= (((m1_subset_1 @ sk_F @ sk_C_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['2'])).
% 1.80/1.98  thf('62', plain,
% 1.80/1.98      (((r2_hidden @ sk_F @ sk_B_1)) <= (((r2_hidden @ sk_F @ sk_B_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['7'])).
% 1.80/1.98  thf('63', plain,
% 1.80/1.98      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['0'])).
% 1.80/1.98  thf('64', plain,
% 1.80/1.98      ((![X36 : $i]:
% 1.80/1.98          (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98           | ~ (r2_hidden @ X36 @ sk_B_1)))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))))),
% 1.80/1.98      inference('split', [status(esa)], ['38'])).
% 1.80/1.98  thf('65', plain,
% 1.80/1.98      (((~ (r2_hidden @ sk_F @ sk_B_1) | ~ (m1_subset_1 @ sk_F @ sk_C_1)))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['63', '64'])).
% 1.80/1.98  thf('66', plain,
% 1.80/1.98      ((~ (m1_subset_1 @ sk_F @ sk_C_1))
% 1.80/1.98         <= ((![X36 : $i]:
% 1.80/1.98                (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98                 | ~ (r2_hidden @ X36 @ sk_B_1))) & 
% 1.80/1.98             ((r2_hidden @ sk_F @ sk_B_1)) & 
% 1.80/1.98             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['62', '65'])).
% 1.80/1.98  thf('67', plain,
% 1.80/1.98      (~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 1.80/1.98       ~
% 1.80/1.98       (![X36 : $i]:
% 1.80/1.98          (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98           | ~ (r2_hidden @ X36 @ sk_B_1))) | 
% 1.80/1.98       ~ ((m1_subset_1 @ sk_F @ sk_C_1)) | ~ ((r2_hidden @ sk_F @ sk_B_1))),
% 1.80/1.98      inference('sup-', [status(thm)], ['61', '66'])).
% 1.80/1.98  thf('68', plain,
% 1.80/1.98      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))) | 
% 1.80/1.98       (![X36 : $i]:
% 1.80/1.98          (~ (m1_subset_1 @ X36 @ sk_C_1)
% 1.80/1.98           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_E) @ sk_D_1)
% 1.80/1.98           | ~ (r2_hidden @ X36 @ sk_B_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['38'])).
% 1.80/1.98  thf('69', plain,
% 1.80/1.98      (((r2_hidden @ sk_F @ sk_B_1)) | 
% 1.80/1.98       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['7'])).
% 1.80/1.98  thf('70', plain,
% 1.80/1.98      (((r2_hidden @ sk_F @ sk_B_1)) <= (((r2_hidden @ sk_F @ sk_B_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['7'])).
% 1.80/1.98  thf('71', plain,
% 1.80/1.98      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['0'])).
% 1.80/1.98  thf('72', plain,
% 1.80/1.98      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.80/1.98         (~ (r2_hidden @ X21 @ X22)
% 1.80/1.98          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X24)
% 1.80/1.98          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X24))
% 1.80/1.98          | (r2_hidden @ X23 @ (k9_relat_1 @ X24 @ X22))
% 1.80/1.98          | ~ (v1_relat_1 @ X24))),
% 1.80/1.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.80/1.98  thf('73', plain,
% 1.80/1.98      ((![X0 : $i]:
% 1.80/1.98          (~ (v1_relat_1 @ sk_D_1)
% 1.80/1.98           | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 1.80/1.98           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))
% 1.80/1.98           | ~ (r2_hidden @ sk_F @ X0)))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['71', '72'])).
% 1.80/1.98  thf('74', plain, ((v1_relat_1 @ sk_D_1)),
% 1.80/1.98      inference('demod', [status(thm)], ['14', '15'])).
% 1.80/1.98  thf('75', plain,
% 1.80/1.98      ((![X0 : $i]:
% 1.80/1.98          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 1.80/1.98           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))
% 1.80/1.98           | ~ (r2_hidden @ sk_F @ X0)))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('demod', [status(thm)], ['73', '74'])).
% 1.80/1.98  thf('76', plain,
% 1.80/1.98      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('split', [status(esa)], ['0'])).
% 1.80/1.98  thf(t20_relat_1, axiom,
% 1.80/1.98    (![A:$i,B:$i,C:$i]:
% 1.80/1.98     ( ( v1_relat_1 @ C ) =>
% 1.80/1.98       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 1.80/1.98         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.80/1.98           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 1.80/1.98  thf('77', plain,
% 1.80/1.98      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.80/1.98         (~ (r2_hidden @ (k4_tarski @ X27 @ X28) @ X29)
% 1.80/1.98          | (r2_hidden @ X27 @ (k1_relat_1 @ X29))
% 1.80/1.98          | ~ (v1_relat_1 @ X29))),
% 1.80/1.98      inference('cnf', [status(esa)], [t20_relat_1])).
% 1.80/1.98  thf('78', plain,
% 1.80/1.98      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['76', '77'])).
% 1.80/1.98  thf('79', plain, ((v1_relat_1 @ sk_D_1)),
% 1.80/1.98      inference('demod', [status(thm)], ['14', '15'])).
% 1.80/1.98  thf('80', plain,
% 1.80/1.98      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1)))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('demod', [status(thm)], ['78', '79'])).
% 1.80/1.98  thf('81', plain,
% 1.80/1.98      ((![X0 : $i]:
% 1.80/1.98          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 1.80/1.98           | ~ (r2_hidden @ sk_F @ X0)))
% 1.80/1.98         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('demod', [status(thm)], ['75', '80'])).
% 1.80/1.98  thf('82', plain,
% 1.80/1.98      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 1.80/1.98         <= (((r2_hidden @ sk_F @ sk_B_1)) & 
% 1.80/1.98             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['70', '81'])).
% 1.80/1.98  thf('83', plain,
% 1.80/1.98      (![X0 : $i]:
% 1.80/1.98         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ X0)
% 1.80/1.98           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.80/1.98      inference('sup-', [status(thm)], ['4', '5'])).
% 1.80/1.98  thf('84', plain,
% 1.80/1.98      ((~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))
% 1.80/1.98         <= (~
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('split', [status(esa)], ['38'])).
% 1.80/1.98  thf('85', plain,
% 1.80/1.98      ((~ (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 1.80/1.98         <= (~
% 1.80/1.98             ((r2_hidden @ sk_E @ 
% 1.80/1.98               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1))))),
% 1.80/1.98      inference('sup-', [status(thm)], ['83', '84'])).
% 1.80/1.98  thf('86', plain,
% 1.80/1.98      (~ ((r2_hidden @ sk_F @ sk_B_1)) | 
% 1.80/1.98       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 1.80/1.98       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_B_1)))),
% 1.80/1.98      inference('sup-', [status(thm)], ['82', '85'])).
% 1.80/1.98  thf('87', plain, ($false),
% 1.80/1.98      inference('sat_resolution*', [status(thm)],
% 1.80/1.98                ['1', '3', '60', '67', '68', '69', '86'])).
% 1.80/1.98  
% 1.80/1.98  % SZS output end Refutation
% 1.80/1.98  
% 1.80/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
