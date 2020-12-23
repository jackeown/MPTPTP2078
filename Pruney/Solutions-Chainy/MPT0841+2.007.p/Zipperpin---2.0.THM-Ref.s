%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CkmwIW6una

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:23 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 242 expanded)
%              Number of leaves         :   30 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  988 (3620 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ X0 )
      = ( k9_relat_1 @ sk_D_4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_E_1 ) @ sk_D_4 ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_E_1 ) @ sk_D_4 )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_D_4 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D_4 )
    | ( sk_D_4
      = ( k7_relat_1 @ sk_D_4 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,
    ( sk_D_4
    = ( k7_relat_1 @ sk_D_4 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_4 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_4 @ sk_C_1 ) )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( sk_D_4
    = ( k7_relat_1 @ sk_D_4 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('29',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['14','15'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_4 )
      | ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('34',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_E_1 ) @ sk_D_4 )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('36',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
      | ~ ( r2_hidden @ X32 @ sk_B )
      | ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
        | ~ ( r2_hidden @ X32 @ sk_B ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
        | ~ ( r2_hidden @ X32 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_C_1 ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
          | ~ ( r2_hidden @ X32 @ sk_B ) )
      & ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_3 @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_4 )
      | ( r2_hidden @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['14','15'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_B )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1 ) @ sk_C_1 )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
          | ~ ( r2_hidden @ X32 @ sk_B ) )
      & ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) )
    | ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
          | ~ ( r2_hidden @ X32 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( m1_subset_1 @ sk_F @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('47',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
        | ~ ( r2_hidden @ X32 @ sk_B ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
        | ~ ( r2_hidden @ X32 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('50',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C_1 ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
          | ~ ( r2_hidden @ X32 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
          | ~ ( r2_hidden @ X32 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 )
    | ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
          | ~ ( r2_hidden @ X32 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) )
    | ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X32 @ sk_E_1 ) @ sk_D_4 )
        | ~ ( r2_hidden @ X32 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('54',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('55',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('56',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_4 )
        | ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_4 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['14','15'])).

thf('60',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('62',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_4 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ),
    inference(demod,[status(thm)],['58','59','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ X0 )
      = ( k9_relat_1 @ sk_D_4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','45','52','53','54','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CkmwIW6una
% 0.13/0.36  % Computer   : n003.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:35:42 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 195 iterations in 0.121s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.58  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.58  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.38/0.58  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.38/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.38/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(t52_relset_1, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( m1_subset_1 @
% 0.38/0.58                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( m1_subset_1 @ E @ A ) =>
% 0.38/0.58                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.38/0.58                         ( ?[F:$i]:
% 0.38/0.58                           ( ( r2_hidden @ F @ B ) & 
% 0.38/0.58                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.38/0.58                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.58              ( ![C:$i]:
% 0.38/0.58                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.38/0.58                  ( ![D:$i]:
% 0.38/0.58                    ( ( m1_subset_1 @
% 0.38/0.58                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.38/0.58                      ( ![E:$i]:
% 0.38/0.58                        ( ( m1_subset_1 @ E @ A ) =>
% 0.38/0.58                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.38/0.58                            ( ?[F:$i]:
% 0.38/0.58                              ( ( r2_hidden @ F @ B ) & 
% 0.38/0.58                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.38/0.58                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)
% 0.38/0.58        | (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)) | 
% 0.38/0.58       ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_F @ sk_C_1)
% 0.38/0.58        | (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_F @ sk_C_1)) | 
% 0.38/0.58       ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['2'])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.38/0.58          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ X0)
% 0.38/0.58           = (k9_relat_1 @ sk_D_4 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (((r2_hidden @ sk_F @ sk_B)
% 0.38/0.58        | (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('split', [status(esa)], ['7'])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ sk_B)))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['6', '8'])).
% 0.38/0.58  thf(t143_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ C ) =>
% 0.38/0.58       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.38/0.58         ( ?[D:$i]:
% 0.38/0.58           ( ( r2_hidden @ D @ B ) & 
% 0.38/0.58             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.38/0.58             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X22 @ X20 @ X21) @ X21) @ X22)
% 0.38/0.58          | ~ (v1_relat_1 @ X22))),
% 0.38/0.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (((~ (v1_relat_1 @ sk_D_4)
% 0.38/0.58         | (r2_hidden @ 
% 0.38/0.58            (k4_tarski @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_E_1) @ sk_D_4)))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.38/0.58          | (v1_relat_1 @ X2)
% 0.38/0.58          | ~ (v1_relat_1 @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_D_4))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf(fc6_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.58  thf('16', plain, ((v1_relat_1 @ sk_D_4)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (((r2_hidden @ 
% 0.38/0.58         (k4_tarski @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_E_1) @ sk_D_4))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '16'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         ((v4_relat_1 @ X25 @ X26)
% 0.38/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.58  thf('20', plain, ((v4_relat_1 @ sk_D_4 @ sk_C_1)),
% 0.38/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.58  thf(t209_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.58       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X23 : $i, X24 : $i]:
% 0.38/0.58         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.38/0.58          | ~ (v4_relat_1 @ X23 @ X24)
% 0.38/0.58          | ~ (v1_relat_1 @ X23))),
% 0.38/0.58      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_D_4) | ((sk_D_4) = (k7_relat_1 @ sk_D_4 @ sk_C_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('23', plain, ((v1_relat_1 @ sk_D_4)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('24', plain, (((sk_D_4) = (k7_relat_1 @ sk_D_4 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf(d11_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i,C:$i]:
% 0.38/0.58         ( ( v1_relat_1 @ C ) =>
% 0.38/0.58           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.38/0.58             ( ![D:$i,E:$i]:
% 0.38/0.58               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.38/0.58                 ( ( r2_hidden @ D @ B ) & 
% 0.38/0.58                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X4)
% 0.38/0.58          | ((X4) != (k7_relat_1 @ X5 @ X6))
% 0.38/0.58          | (r2_hidden @ X7 @ X6)
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X4)
% 0.38/0.58          | ~ (v1_relat_1 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X5)
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k7_relat_1 @ X5 @ X6))
% 0.38/0.58          | (r2_hidden @ X7 @ X6)
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_D_4)
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D_4 @ sk_C_1))
% 0.38/0.58          | (r2_hidden @ X1 @ sk_C_1)
% 0.38/0.58          | ~ (v1_relat_1 @ sk_D_4))),
% 0.38/0.58      inference('sup-', [status(thm)], ['24', '26'])).
% 0.38/0.58  thf('28', plain, (((sk_D_4) = (k7_relat_1 @ sk_D_4 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf('29', plain, ((v1_relat_1 @ sk_D_4)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('30', plain, ((v1_relat_1 @ sk_D_4)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_D_4)
% 0.38/0.58          | (r2_hidden @ X1 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (((r2_hidden @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_C_1))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '31'])).
% 0.38/0.58  thf(t1_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (((m1_subset_1 @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_C_1))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (((r2_hidden @ 
% 0.38/0.58         (k4_tarski @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_E_1) @ sk_D_4))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('demod', [status(thm)], ['11', '16'])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X32 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58          | ~ (r2_hidden @ X32 @ sk_B)
% 0.38/0.58          | ~ (r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      ((![X32 : $i]:
% 0.38/0.58          (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58           | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58           | ~ (r2_hidden @ X32 @ sk_B)))
% 0.38/0.58         <= ((![X32 : $i]:
% 0.38/0.58                (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58                 | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58                 | ~ (r2_hidden @ X32 @ sk_B))))),
% 0.38/0.58      inference('split', [status(esa)], ['36'])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (((~ (r2_hidden @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_B)
% 0.38/0.58         | ~ (m1_subset_1 @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_C_1)))
% 0.38/0.58         <= ((![X32 : $i]:
% 0.38/0.58                (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58                 | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58                 | ~ (r2_hidden @ X32 @ sk_B))) & 
% 0.38/0.58             ((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['35', '37'])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ sk_B)))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup+', [status(thm)], ['6', '8'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.38/0.58          | (r2_hidden @ (sk_D_3 @ X22 @ X20 @ X21) @ X20)
% 0.38/0.58          | ~ (v1_relat_1 @ X22))),
% 0.38/0.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (((~ (v1_relat_1 @ sk_D_4)
% 0.38/0.58         | (r2_hidden @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_B)))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.58  thf('42', plain, ((v1_relat_1 @ sk_D_4)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (((r2_hidden @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_B))
% 0.38/0.58         <= (((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ (sk_D_3 @ sk_D_4 @ sk_B @ sk_E_1) @ sk_C_1))
% 0.38/0.58         <= ((![X32 : $i]:
% 0.38/0.58                (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58                 | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58                 | ~ (r2_hidden @ X32 @ sk_B))) & 
% 0.38/0.58             ((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('demod', [status(thm)], ['38', '43'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (~ ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))) | 
% 0.38/0.58       ~
% 0.38/0.58       (![X32 : $i]:
% 0.38/0.58          (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58           | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58           | ~ (r2_hidden @ X32 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['34', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_F @ sk_C_1)) <= (((m1_subset_1 @ sk_F @ sk_C_1)))),
% 0.38/0.58      inference('split', [status(esa)], ['2'])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['7'])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4))
% 0.38/0.58         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      ((![X32 : $i]:
% 0.38/0.58          (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58           | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58           | ~ (r2_hidden @ X32 @ sk_B)))
% 0.38/0.58         <= ((![X32 : $i]:
% 0.38/0.58                (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58                 | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58                 | ~ (r2_hidden @ X32 @ sk_B))))),
% 0.38/0.58      inference('split', [status(esa)], ['36'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C_1)))
% 0.38/0.58         <= ((![X32 : $i]:
% 0.38/0.58                (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58                 | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58                 | ~ (r2_hidden @ X32 @ sk_B))) & 
% 0.38/0.58             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ sk_F @ sk_C_1))
% 0.38/0.58         <= ((![X32 : $i]:
% 0.38/0.58                (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58                 | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58                 | ~ (r2_hidden @ X32 @ sk_B))) & 
% 0.38/0.58             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.38/0.58             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['47', '50'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)) | 
% 0.38/0.58       ~
% 0.38/0.58       (![X32 : $i]:
% 0.38/0.58          (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58           | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58           | ~ (r2_hidden @ X32 @ sk_B))) | 
% 0.38/0.58       ~ ((m1_subset_1 @ sk_F @ sk_C_1)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['46', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (~ ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))) | 
% 0.38/0.58       (![X32 : $i]:
% 0.38/0.58          (~ (m1_subset_1 @ X32 @ sk_C_1)
% 0.38/0.58           | ~ (r2_hidden @ (k4_tarski @ X32 @ sk_E_1) @ sk_D_4)
% 0.38/0.58           | ~ (r2_hidden @ X32 @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['36'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.38/0.58       ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['7'])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['7'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4))
% 0.38/0.58         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X19 @ X20)
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X22)
% 0.38/0.58          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X22))
% 0.38/0.58          | (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.38/0.58          | ~ (v1_relat_1 @ X22))),
% 0.38/0.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          (~ (v1_relat_1 @ sk_D_4)
% 0.38/0.58           | (r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ X0))
% 0.38/0.58           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_4))
% 0.38/0.58           | ~ (r2_hidden @ sk_F @ X0)))
% 0.38/0.58         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf('59', plain, ((v1_relat_1 @ sk_D_4)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4))
% 0.38/0.58         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf(d4_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.38/0.58       ( ![C:$i]:
% 0.38/0.58         ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.58           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.38/0.58          | (r2_hidden @ X10 @ X13)
% 0.38/0.58          | ((X13) != (k1_relat_1 @ X12)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.58         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.38/0.58      inference('simplify', [status(thm)], ['61'])).
% 0.38/0.58  thf('63', plain,
% 0.38/0.58      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_4)))
% 0.38/0.58         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['60', '62'])).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ X0))
% 0.38/0.58           | ~ (r2_hidden @ sk_F @ X0)))
% 0.38/0.58         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('demod', [status(thm)], ['58', '59', '63'])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ sk_B)))
% 0.38/0.58         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.38/0.58             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['55', '64'])).
% 0.38/0.58  thf('66', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ X0)
% 0.38/0.58           = (k9_relat_1 @ sk_D_4 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      ((~ (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('split', [status(esa)], ['36'])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      ((~ (r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ sk_B)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r2_hidden @ sk_E_1 @ 
% 0.38/0.58               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.38/0.58       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)) | 
% 0.38/0.58       ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_4 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['65', '68'])).
% 0.38/0.58  thf('70', plain, ($false),
% 0.38/0.58      inference('sat_resolution*', [status(thm)],
% 0.38/0.58                ['1', '3', '45', '52', '53', '54', '69'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
