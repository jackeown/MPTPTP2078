%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tOji7x7pMM

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:23 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 685 expanded)
%              Number of leaves         :   31 ( 210 expanded)
%              Depth                    :   17
%              Number of atoms          :  880 (9954 expanded)
%              Number of equality atoms :   11 (  79 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

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

thf('0',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E_1 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X28 @ sk_B )
      | ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) )
    | ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E_1 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_D_2 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( sk_D_2
      = ( k7_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('25',plain,
    ( sk_D_2
    = ( k7_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ sk_C ) )
      | ( r2_hidden @ X1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( sk_D_2
    = ( k7_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_2 )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('37',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E_1 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E_1 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_C ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E_1 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_B )
   <= ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1 ) @ sk_C )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E_1 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_E_1 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['6','45'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['5','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('50',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference('sat_resolution*',[status(thm)],['6','45','49'])).

thf('51',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['52'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['6','45','54'])).

thf('56',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 ),
    inference(simpl_trail,[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_2 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_2 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['52'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('63',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('65',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['6','45','54'])).

thf('67',plain,(
    r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['47','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tOji7x7pMM
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 121 iterations in 0.080s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.34/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.34/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.34/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.34/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.52  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(t52_relset_1, conjecture,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.34/0.52               ( ![D:$i]:
% 0.34/0.52                 ( ( m1_subset_1 @
% 0.34/0.52                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.34/0.52                   ( ![E:$i]:
% 0.34/0.52                     ( ( m1_subset_1 @ E @ A ) =>
% 0.34/0.52                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.34/0.52                         ( ?[F:$i]:
% 0.34/0.52                           ( ( r2_hidden @ F @ B ) & 
% 0.34/0.52                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.34/0.52                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]:
% 0.34/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.52          ( ![B:$i]:
% 0.34/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.34/0.52              ( ![C:$i]:
% 0.34/0.52                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.34/0.52                  ( ![D:$i]:
% 0.34/0.52                    ( ( m1_subset_1 @
% 0.34/0.52                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.34/0.52                      ( ![E:$i]:
% 0.34/0.52                        ( ( m1_subset_1 @ E @ A ) =>
% 0.34/0.52                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.34/0.52                            ( ?[F:$i]:
% 0.34/0.52                              ( ( r2_hidden @ F @ B ) & 
% 0.34/0.52                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.34/0.52                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (![X28 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X28 @ sk_C)
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E_1) @ sk_D_2)
% 0.34/0.52          | ~ (r2_hidden @ X28 @ sk_B)
% 0.34/0.52          | ~ (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      ((~ (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))
% 0.34/0.52         <= (~
% 0.34/0.52             ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.34/0.52          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0)
% 0.34/0.52           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      ((~ (r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.34/0.52         <= (~
% 0.34/0.52             ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['1', '4'])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (~ ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))) | 
% 0.34/0.52       (![X28 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E_1) @ sk_D_2)
% 0.34/0.52           | ~ (r2_hidden @ X28 @ sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0)
% 0.34/0.52           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (((r2_hidden @ sk_F @ sk_B)
% 0.34/0.52        | (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['8'])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['7', '9'])).
% 0.34/0.52  thf(t143_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ C ) =>
% 0.34/0.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.34/0.52         ( ?[D:$i]:
% 0.34/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.34/0.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.34/0.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.34/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X15 @ X13 @ X14) @ X14) @ X15)
% 0.34/0.52          | ~ (v1_relat_1 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (((~ (v1_relat_1 @ sk_D_2)
% 0.34/0.52         | (r2_hidden @ 
% 0.34/0.52            (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_E_1) @ sk_D_2)))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc2_relat_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X2 : $i, X3 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.34/0.52          | (v1_relat_1 @ X2)
% 0.34/0.52          | ~ (v1_relat_1 @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D_2))),
% 0.34/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf(fc6_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.34/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.52  thf('17', plain, ((v1_relat_1 @ sk_D_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (((r2_hidden @ 
% 0.34/0.52         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_E_1) @ sk_D_2))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['12', '17'])).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc2_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.34/0.52         ((v4_relat_1 @ X21 @ X22)
% 0.34/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.52  thf('21', plain, ((v4_relat_1 @ sk_D_2 @ sk_C)),
% 0.34/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.52  thf(t209_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i]:
% 0.34/0.52         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.34/0.52          | ~ (v4_relat_1 @ X16 @ X17)
% 0.34/0.52          | ~ (v1_relat_1 @ X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ sk_D_2) | ((sk_D_2) = (k7_relat_1 @ sk_D_2 @ sk_C)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.34/0.52  thf('24', plain, ((v1_relat_1 @ sk_D_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('25', plain, (((sk_D_2) = (k7_relat_1 @ sk_D_2 @ sk_C))),
% 0.34/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.34/0.52  thf(d11_relat_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ A ) =>
% 0.34/0.52       ( ![B:$i,C:$i]:
% 0.34/0.52         ( ( v1_relat_1 @ C ) =>
% 0.34/0.52           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.34/0.52             ( ![D:$i,E:$i]:
% 0.34/0.52               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.34/0.52                 ( ( r2_hidden @ D @ B ) & 
% 0.34/0.52                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X4)
% 0.34/0.52          | ((X4) != (k7_relat_1 @ X5 @ X6))
% 0.34/0.52          | (r2_hidden @ X7 @ X6)
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X4)
% 0.34/0.52          | ~ (v1_relat_1 @ X5))),
% 0.34/0.52      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X5)
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k7_relat_1 @ X5 @ X6))
% 0.34/0.52          | (r2_hidden @ X7 @ X6)
% 0.34/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_D_2)
% 0.34/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D_2 @ sk_C))
% 0.34/0.52          | (r2_hidden @ X1 @ sk_C)
% 0.34/0.52          | ~ (v1_relat_1 @ sk_D_2))),
% 0.34/0.52      inference('sup-', [status(thm)], ['25', '27'])).
% 0.34/0.52  thf('29', plain, (((sk_D_2) = (k7_relat_1 @ sk_D_2 @ sk_C))),
% 0.34/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.34/0.52  thf('30', plain, ((v1_relat_1 @ sk_D_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('31', plain, ((v1_relat_1 @ sk_D_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_D_2)
% 0.34/0.52          | (r2_hidden @ X1 @ sk_C))),
% 0.34/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_C))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['18', '32'])).
% 0.34/0.52  thf(t1_subset, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_C))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      (((r2_hidden @ 
% 0.34/0.52         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_E_1) @ sk_D_2))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['12', '17'])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      ((![X28 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E_1) @ sk_D_2)
% 0.34/0.52           | ~ (r2_hidden @ X28 @ sk_B)))
% 0.34/0.52         <= ((![X28 : $i]:
% 0.34/0.52                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.34/0.52                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E_1) @ sk_D_2)
% 0.34/0.52                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_B)
% 0.34/0.52         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_C)))
% 0.34/0.52         <= ((![X28 : $i]:
% 0.34/0.52                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.34/0.52                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E_1) @ sk_D_2)
% 0.34/0.52                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.34/0.52             ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      (((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['7', '9'])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.34/0.52          | (r2_hidden @ (sk_D_1 @ X15 @ X13 @ X14) @ X13)
% 0.34/0.52          | ~ (v1_relat_1 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      (((~ (v1_relat_1 @ sk_D_2)
% 0.34/0.52         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_B)))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.52  thf('42', plain, ((v1_relat_1 @ sk_D_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_B))
% 0.34/0.52         <= (((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_1) @ sk_C))
% 0.34/0.52         <= ((![X28 : $i]:
% 0.34/0.52                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.34/0.52                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E_1) @ sk_D_2)
% 0.34/0.52                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.34/0.52             ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['38', '43'])).
% 0.34/0.52  thf('45', plain,
% 0.34/0.52      (~
% 0.34/0.52       (![X28 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_E_1) @ sk_D_2)
% 0.34/0.52           | ~ (r2_hidden @ X28 @ sk_B))) | 
% 0.34/0.52       ~ ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['35', '44'])).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      (~ ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['6', '45'])).
% 0.34/0.52  thf('47', plain, (~ (r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_B))),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['5', '46'])).
% 0.34/0.52  thf('48', plain,
% 0.34/0.52      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['8'])).
% 0.34/0.52  thf('49', plain,
% 0.34/0.52      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.34/0.52       ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['8'])).
% 0.34/0.52  thf('50', plain, (((r2_hidden @ sk_F @ sk_B))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['6', '45', '49'])).
% 0.34/0.52  thf('51', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.34/0.52  thf('52', plain,
% 0.34/0.52      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2)
% 0.34/0.52        | (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('53', plain,
% 0.34/0.52      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2)))),
% 0.34/0.52      inference('split', [status(esa)], ['52'])).
% 0.34/0.52  thf('54', plain,
% 0.34/0.52      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2)) | 
% 0.34/0.52       ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['52'])).
% 0.34/0.52  thf('55', plain, (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['6', '45', '54'])).
% 0.34/0.52  thf('56', plain, ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2)),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['53', '55'])).
% 0.34/0.52  thf('57', plain,
% 0.34/0.52      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X12 @ X13)
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X15)
% 0.34/0.52          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X15))
% 0.34/0.52          | (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.34/0.52          | ~ (v1_relat_1 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('58', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ sk_D_2)
% 0.34/0.52          | (r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ X0))
% 0.34/0.52          | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_2))
% 0.34/0.52          | ~ (r2_hidden @ sk_F @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.52  thf('59', plain, ((v1_relat_1 @ sk_D_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('60', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ X0))
% 0.34/0.52          | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_2))
% 0.34/0.52          | ~ (r2_hidden @ sk_F @ X0))),
% 0.34/0.52      inference('demod', [status(thm)], ['58', '59'])).
% 0.34/0.52  thf('61', plain,
% 0.34/0.52      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2)))),
% 0.34/0.52      inference('split', [status(esa)], ['52'])).
% 0.34/0.52  thf(t20_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ C ) =>
% 0.34/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.34/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.34/0.52           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.34/0.52  thf('62', plain,
% 0.34/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.34/0.52         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.34/0.52          | (r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 0.34/0.52          | ~ (v1_relat_1 @ X20))),
% 0.34/0.52      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.34/0.52  thf('63', plain,
% 0.34/0.52      (((~ (v1_relat_1 @ sk_D_2) | (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_2))))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.34/0.52  thf('64', plain, ((v1_relat_1 @ sk_D_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('65', plain,
% 0.34/0.52      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_2)))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2)))),
% 0.34/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.34/0.52  thf('66', plain, (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_2))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['6', '45', '54'])).
% 0.34/0.52  thf('67', plain, ((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_2))),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.34/0.52  thf('68', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ X0))
% 0.34/0.52          | ~ (r2_hidden @ sk_F @ X0))),
% 0.34/0.52      inference('demod', [status(thm)], ['60', '67'])).
% 0.34/0.52  thf('69', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['51', '68'])).
% 0.34/0.52  thf('70', plain, ($false), inference('demod', [status(thm)], ['47', '69'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.39/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
