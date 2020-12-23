%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nuLkFFBq3A

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:56 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 172 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  717 (2038 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_3 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k7_relset_1 @ X33 @ X34 @ X35 @ X33 )
        = ( k2_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('10',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('15',plain,
    ( ( k9_relat_1 @ sk_C_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_3 ) @ sk_C_1 ) )
   <= ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_3 ) @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('28',plain,
    ( ( k9_relat_1 @ sk_C_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,
    ( ~ ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nuLkFFBq3A
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 116 iterations in 0.131s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.60  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(t48_relset_1, conjecture,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.38/0.60               ( ![D:$i]:
% 0.38/0.60                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.38/0.60                   ( ?[E:$i]:
% 0.38/0.60                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.38/0.60                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]:
% 0.38/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.60          ( ![B:$i]:
% 0.38/0.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.60              ( ![C:$i]:
% 0.38/0.60                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.38/0.60                  ( ![D:$i]:
% 0.38/0.60                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.38/0.60                      ( ?[E:$i]:
% 0.38/0.60                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.38/0.60                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (![X36 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X36 @ sk_B)
% 0.38/0.60          | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_3) @ sk_C_1)
% 0.38/0.60          | ~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      ((![X36 : $i]:
% 0.38/0.60          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_3) @ sk_C_1))) | 
% 0.38/0.60       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.38/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)
% 0.38/0.60        | (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('split', [status(esa)], ['5'])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['4', '6'])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t38_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.38/0.60         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.60         (((k7_relset_1 @ X33 @ X34 @ X35 @ X33)
% 0.38/0.60            = (k2_relset_1 @ X33 @ X34 @ X35))
% 0.38/0.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.38/0.60      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (((k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ sk_B)
% 0.38/0.60         = (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.38/0.60          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ X0)
% 0.38/0.60           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('15', plain, (((k9_relat_1 @ sk_C_1 @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.38/0.60  thf(t143_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ C ) =>
% 0.38/0.60       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.38/0.60         ( ?[D:$i]:
% 0.38/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.38/0.60             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.38/0.60             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.38/0.60          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X22 @ X20 @ X21) @ X21) @ X22)
% 0.38/0.60          | ~ (v1_relat_1 @ X22))),
% 0.38/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.60          | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.60          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.38/0.60             sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X6 : $i, X7 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.38/0.60          | (v1_relat_1 @ X6)
% 0.38/0.60          | ~ (v1_relat_1 @ X7))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf(fc6_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.60  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.60          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.38/0.60             sk_C_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['17', '22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (((r2_hidden @ 
% 0.38/0.60         (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_D_3) @ sk_C_1))
% 0.38/0.60         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['7', '23'])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      ((![X36 : $i]:
% 0.38/0.60          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_3) @ sk_C_1)))
% 0.38/0.60         <= ((![X36 : $i]:
% 0.38/0.60                (~ (m1_subset_1 @ X36 @ sk_B)
% 0.38/0.60                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_3) @ sk_C_1))))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.38/0.60         <= ((![X36 : $i]:
% 0.38/0.60                (~ (m1_subset_1 @ X36 @ sk_B)
% 0.38/0.60                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_3) @ sk_C_1))) & 
% 0.38/0.60             ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['4', '6'])).
% 0.38/0.60  thf('28', plain, (((k9_relat_1 @ sk_C_1 @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.38/0.60          | (r2_hidden @ (sk_D_2 @ X22 @ X20 @ X21) @ (k1_relat_1 @ X22))
% 0.38/0.60          | ~ (v1_relat_1 @ X22))),
% 0.38/0.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.60          | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.60          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_C_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.60          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_C_1)))),
% 0.38/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ (k1_relat_1 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['27', '32'])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.60         ((v4_relat_1 @ X23 @ X24)
% 0.38/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('36', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.60  thf(d18_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i]:
% 0.38/0.60         (~ (v4_relat_1 @ X8 @ X9)
% 0.38/0.60          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.38/0.60          | ~ (v1_relat_1 @ X8))),
% 0.38/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.60  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.60  thf(t3_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (![X0 : $i, X2 : $i]:
% 0.38/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.60  thf(t4_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.60       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X3 @ X4)
% 0.38/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.38/0.60          | (m1_subset_1 @ X3 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((m1_subset_1 @ X0 @ sk_B)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.38/0.60         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['33', '44'])).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (~
% 0.38/0.60       (![X36 : $i]:
% 0.38/0.60          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_3) @ sk_C_1))) | 
% 0.38/0.60       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.38/0.60      inference('demod', [status(thm)], ['26', '45'])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.38/0.60       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.38/0.60      inference('split', [status(esa)], ['5'])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))
% 0.38/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.38/0.60      inference('split', [status(esa)], ['5'])).
% 0.38/0.60  thf(d5_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.60       ( ![C:$i]:
% 0.38/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.60         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.38/0.60          | (r2_hidden @ X11 @ X13)
% 0.38/0.60          | ((X13) != (k2_relat_1 @ X12)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.38/0.60  thf('50', plain,
% 0.38/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.60         ((r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.38/0.60          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.38/0.60      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['48', '50'])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      ((~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.38/0.60         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      ((~ (r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.38/0.60         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.38/0.60       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['51', '54'])).
% 0.38/0.60  thf('56', plain, ($false),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '55'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
