%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1BpTDOt7rZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:01 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 122 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  627 (1185 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('9',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ X0 @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ X0 @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['9','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X39 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['7','42'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X17: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1BpTDOt7rZ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.06/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.29  % Solved by: fo/fo7.sh
% 1.06/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.29  % done 1378 iterations in 0.827s
% 1.06/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.29  % SZS output start Refutation
% 1.06/1.29  thf(sk_B_type, type, sk_B: $i > $i).
% 1.06/1.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.06/1.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.06/1.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.29  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.06/1.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.29  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.06/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.29  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.06/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.29  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.29  thf(d10_xboole_0, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.29  thf('0', plain,
% 1.06/1.29      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.06/1.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.29  thf('1', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.06/1.29      inference('simplify', [status(thm)], ['0'])).
% 1.06/1.29  thf(t49_relset_1, conjecture,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.06/1.29           ( ![C:$i]:
% 1.06/1.29             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.29               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 1.06/1.29                    ( ![D:$i]:
% 1.06/1.29                      ( ( m1_subset_1 @ D @ B ) =>
% 1.06/1.29                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.29    (~( ![A:$i]:
% 1.06/1.29        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.29          ( ![B:$i]:
% 1.06/1.29            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.06/1.29              ( ![C:$i]:
% 1.06/1.29                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.29                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 1.06/1.29                       ( ![D:$i]:
% 1.06/1.29                         ( ( m1_subset_1 @ D @ B ) =>
% 1.06/1.29                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.06/1.29    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 1.06/1.29  thf('2', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(t14_relset_1, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.29     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.06/1.29       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 1.06/1.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 1.06/1.29  thf('3', plain,
% 1.06/1.29      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.29         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 1.06/1.29          | (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 1.06/1.29          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.06/1.29      inference('cnf', [status(esa)], [t14_relset_1])).
% 1.06/1.29  thf('4', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.06/1.29          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 1.06/1.29      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.29  thf('5', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 1.06/1.29      inference('sup-', [status(thm)], ['1', '4'])).
% 1.06/1.29  thf(cc4_relset_1, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( v1_xboole_0 @ A ) =>
% 1.06/1.29       ( ![C:$i]:
% 1.06/1.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.06/1.29           ( v1_xboole_0 @ C ) ) ) ))).
% 1.06/1.29  thf('6', plain,
% 1.06/1.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.06/1.29         (~ (v1_xboole_0 @ X26)
% 1.06/1.29          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 1.06/1.29          | (v1_xboole_0 @ X27))),
% 1.06/1.29      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.06/1.29  thf('7', plain,
% 1.06/1.29      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['5', '6'])).
% 1.06/1.29  thf(t146_relat_1, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( v1_relat_1 @ A ) =>
% 1.06/1.29       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.06/1.29  thf('8', plain,
% 1.06/1.29      (![X22 : $i]:
% 1.06/1.29         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 1.06/1.29          | ~ (v1_relat_1 @ X22))),
% 1.06/1.29      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.06/1.29  thf('9', plain,
% 1.06/1.29      (![X22 : $i]:
% 1.06/1.29         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 1.06/1.29          | ~ (v1_relat_1 @ X22))),
% 1.06/1.29      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.06/1.29  thf(existence_m1_subset_1, axiom,
% 1.06/1.29    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 1.06/1.29  thf('10', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 1.06/1.29      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.06/1.29  thf(t2_subset, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( m1_subset_1 @ A @ B ) =>
% 1.06/1.29       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.06/1.29  thf('11', plain,
% 1.06/1.29      (![X15 : $i, X16 : $i]:
% 1.06/1.29         ((r2_hidden @ X15 @ X16)
% 1.06/1.29          | (v1_xboole_0 @ X16)
% 1.06/1.29          | ~ (m1_subset_1 @ X15 @ X16))),
% 1.06/1.29      inference('cnf', [status(esa)], [t2_subset])).
% 1.06/1.29  thf('12', plain,
% 1.06/1.29      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.06/1.29      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.29  thf(t143_relat_1, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i]:
% 1.06/1.29     ( ( v1_relat_1 @ C ) =>
% 1.06/1.29       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.06/1.29         ( ?[D:$i]:
% 1.06/1.29           ( ( r2_hidden @ D @ B ) & 
% 1.06/1.29             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.06/1.29             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.06/1.29  thf('13', plain,
% 1.06/1.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.06/1.29         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 1.06/1.29          | (r2_hidden @ (k4_tarski @ (sk_D @ X21 @ X19 @ X20) @ X20) @ X21)
% 1.06/1.29          | ~ (v1_relat_1 @ X21))),
% 1.06/1.29      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.06/1.29  thf('14', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 1.06/1.29          | ~ (v1_relat_1 @ X1)
% 1.06/1.29          | (r2_hidden @ 
% 1.06/1.29             (k4_tarski @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.06/1.29              (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.06/1.29             X1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['12', '13'])).
% 1.06/1.29  thf('15', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(l3_subset_1, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.29       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.06/1.29  thf('16', plain,
% 1.06/1.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.06/1.29         (~ (r2_hidden @ X10 @ X11)
% 1.06/1.29          | (r2_hidden @ X10 @ X12)
% 1.06/1.29          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.06/1.29      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.06/1.29  thf('17', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.06/1.29          | ~ (r2_hidden @ X0 @ sk_C))),
% 1.06/1.29      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.29  thf('18', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         (~ (v1_relat_1 @ sk_C)
% 1.06/1.29          | (v1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 1.06/1.29          | (r2_hidden @ 
% 1.06/1.29             (k4_tarski @ 
% 1.06/1.29              (sk_D @ sk_C @ X0 @ (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 1.06/1.29              (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 1.06/1.29             (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['14', '17'])).
% 1.06/1.29  thf('19', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(cc1_relset_1, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i]:
% 1.06/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.29       ( v1_relat_1 @ C ) ))).
% 1.06/1.29  thf('20', plain,
% 1.06/1.29      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.29         ((v1_relat_1 @ X23)
% 1.06/1.29          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.06/1.29      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.06/1.29  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.29      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.29  thf('22', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 1.06/1.29          | (r2_hidden @ 
% 1.06/1.29             (k4_tarski @ 
% 1.06/1.29              (sk_D @ sk_C @ X0 @ (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 1.06/1.29              (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 1.06/1.29             (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('demod', [status(thm)], ['18', '21'])).
% 1.06/1.29  thf(l54_zfmisc_1, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.29     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.06/1.29       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.06/1.29  thf('23', plain,
% 1.06/1.29      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.06/1.29         ((r2_hidden @ X6 @ X7)
% 1.06/1.29          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 1.06/1.29      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.06/1.29  thf('24', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 1.06/1.29          | (r2_hidden @ (sk_B @ (k9_relat_1 @ sk_C @ X0)) @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['22', '23'])).
% 1.06/1.29  thf('25', plain,
% 1.06/1.29      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1)
% 1.06/1.29        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.29        | (v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 1.06/1.29      inference('sup+', [status(thm)], ['9', '24'])).
% 1.06/1.29  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.29      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.29  thf('27', plain,
% 1.06/1.29      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1)
% 1.06/1.29        | (v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 1.06/1.29      inference('demod', [status(thm)], ['25', '26'])).
% 1.06/1.29  thf(t1_subset, axiom,
% 1.06/1.29    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.06/1.29  thf('28', plain,
% 1.06/1.29      (![X13 : $i, X14 : $i]:
% 1.06/1.29         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 1.06/1.29      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.29  thf('29', plain,
% 1.06/1.29      (((v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 1.06/1.29        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['27', '28'])).
% 1.06/1.29  thf('30', plain,
% 1.06/1.29      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.06/1.29      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.29  thf('31', plain,
% 1.06/1.29      (![X39 : $i]:
% 1.06/1.29         (~ (r2_hidden @ X39 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 1.06/1.29          | ~ (m1_subset_1 @ X39 @ sk_B_1))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('32', plain,
% 1.06/1.29      (((v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 1.06/1.29        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C)) @ 
% 1.06/1.29             sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['30', '31'])).
% 1.06/1.29  thf('33', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(redefinition_k2_relset_1, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i]:
% 1.06/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.06/1.29  thf('34', plain,
% 1.06/1.29      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.06/1.29         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 1.06/1.29          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.06/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.06/1.29  thf('35', plain,
% 1.06/1.29      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.06/1.29      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.29  thf('36', plain,
% 1.06/1.29      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.06/1.29      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.29  thf('37', plain,
% 1.06/1.29      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.06/1.29        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1))),
% 1.06/1.29      inference('demod', [status(thm)], ['32', '35', '36'])).
% 1.06/1.29  thf('38', plain,
% 1.06/1.29      (((v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 1.06/1.29        | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['29', '37'])).
% 1.06/1.29  thf('39', plain,
% 1.06/1.29      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.06/1.29        | ~ (v1_relat_1 @ sk_C)
% 1.06/1.29        | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 1.06/1.29      inference('sup+', [status(thm)], ['8', '38'])).
% 1.06/1.29  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 1.06/1.29      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.29  thf('41', plain,
% 1.06/1.29      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.06/1.29        | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 1.06/1.29      inference('demod', [status(thm)], ['39', '40'])).
% 1.06/1.29  thf('42', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.06/1.29      inference('simplify', [status(thm)], ['41'])).
% 1.06/1.29  thf('43', plain, ((v1_xboole_0 @ sk_C)),
% 1.06/1.29      inference('demod', [status(thm)], ['7', '42'])).
% 1.06/1.29  thf(fc10_relat_1, axiom,
% 1.06/1.29    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 1.06/1.29  thf('44', plain,
% 1.06/1.29      (![X17 : $i]:
% 1.06/1.29         ((v1_xboole_0 @ (k1_relat_1 @ X17)) | ~ (v1_xboole_0 @ X17))),
% 1.06/1.29      inference('cnf', [status(esa)], [fc10_relat_1])).
% 1.06/1.29  thf(l13_xboole_0, axiom,
% 1.06/1.29    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.06/1.29  thf('45', plain,
% 1.06/1.29      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.29      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.06/1.29  thf('46', plain,
% 1.06/1.29      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf('47', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.06/1.29      inference('sup-', [status(thm)], ['43', '46'])).
% 1.06/1.29  thf('48', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) != (k1_xboole_0))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('49', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(redefinition_k1_relset_1, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i]:
% 1.06/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.29       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.06/1.29  thf('50', plain,
% 1.06/1.29      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.29         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.06/1.29          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.06/1.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.06/1.29  thf('51', plain,
% 1.06/1.29      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.06/1.29      inference('sup-', [status(thm)], ['49', '50'])).
% 1.06/1.29  thf('52', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 1.06/1.29      inference('demod', [status(thm)], ['48', '51'])).
% 1.06/1.29  thf('53', plain, ($false),
% 1.06/1.29      inference('simplify_reflect-', [status(thm)], ['47', '52'])).
% 1.06/1.29  
% 1.06/1.29  % SZS output end Refutation
% 1.06/1.29  
% 1.06/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
