%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfLHaYdYTt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:05 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 253 expanded)
%              Number of leaves         :   35 (  91 expanded)
%              Depth                    :   21
%              Number of atoms          :  725 (2563 expanded)
%              Number of equality atoms :   39 ( 114 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X31 @ ( k3_relset_1 @ X31 @ X32 @ X33 ) )
        = ( k2_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    = ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X34 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('12',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X34 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','22'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['12','27'])).

thf('29',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','33'])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('50',plain,
    ( k1_xboole_0
    = ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','50'])).

thf('52',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X31 @ ( k3_relset_1 @ X31 @ X32 @ X33 ) )
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( k1_xboole_0
    = ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('72',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfLHaYdYTt
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 217 iterations in 0.137s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.58  thf(t49_relset_1, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.40/0.58                    ( ![D:$i]:
% 0.40/0.58                      ( ( m1_subset_1 @ D @ B ) =>
% 0.40/0.58                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58              ( ![C:$i]:
% 0.40/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.40/0.58                       ( ![D:$i]:
% 0.40/0.58                         ( ( m1_subset_1 @ D @ B ) =>
% 0.40/0.58                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(dt_k3_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( m1_subset_1 @
% 0.40/0.58         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.40/0.58         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k3_relset_1 @ X22 @ X23 @ X24) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.40/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t24_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.40/0.58           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.40/0.58         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.40/0.58           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X32 @ X31 @ (k3_relset_1 @ X31 @ X32 @ X33))
% 0.40/0.58            = (k2_relset_1 @ X31 @ X32 @ X33))
% 0.40/0.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.40/0.58      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.40/0.58         = (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.58         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.40/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(d1_xboole_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X34 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X34 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.40/0.58          | ~ (m1_subset_1 @ X34 @ sk_B_1))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X34 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X34 @ (k2_relat_1 @ sk_C))
% 0.40/0.58          | ~ (m1_subset_1 @ X34 @ sk_B_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.58         ((v5_relat_1 @ X19 @ X21)
% 0.40/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.58  thf('15', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf(d19_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         (~ (v5_relat_1 @ X13 @ X14)
% 0.40/0.58          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.40/0.58          | ~ (v1_relat_1 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | (v1_relat_1 @ X11)
% 0.40/0.58          | ~ (v1_relat_1 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf(fc6_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.58  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.58  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['17', '22'])).
% 0.40/0.58  thf(t3_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X5 : $i, X7 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf(t4_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.40/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.40/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.40/0.58          | (m1_subset_1 @ X8 @ X10))),
% 0.40/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.58  thf('28', plain, (![X34 : $i]: ~ (r2_hidden @ X34 @ (k2_relat_1 @ sk_C))),
% 0.40/0.58      inference('clc', [status(thm)], ['12', '27'])).
% 0.40/0.58  thf('29', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '28'])).
% 0.40/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.58  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf(t8_boole, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t8_boole])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.58  thf('33', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['29', '32'])).
% 0.40/0.58  thf('34', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.40/0.58         = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['5', '34'])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.40/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.40/0.58         = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (((k1_xboole_0) = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['35', '38'])).
% 0.40/0.58  thf(fc8_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.40/0.58       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X18 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ (k1_relat_1 @ X18))
% 0.40/0.58          | ~ (v1_relat_1 @ X18)
% 0.40/0.58          | (v1_xboole_0 @ X18))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.58        | (v1_xboole_0 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.40/0.58        | ~ (v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | (v1_relat_1 @ X11)
% 0.40/0.58          | ~ (v1_relat_1 @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))
% 0.40/0.58        | (v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.58  thf('47', plain, ((v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.58  thf('48', plain, ((v1_xboole_0 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['41', '42', '47'])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.58  thf('50', plain, (((k1_xboole_0) = (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['2', '50'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.58         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.40/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0)
% 0.40/0.58         = (k2_relat_1 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.40/0.58  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf(fc11_relat_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (![X15 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ (k2_relat_1 @ X15)) | ~ (v1_xboole_0 @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.58  thf('57', plain,
% 0.40/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k2_relat_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.58  thf('58', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['54', '57'])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['53', '58'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.40/0.58         (((k2_relset_1 @ X32 @ X31 @ (k3_relset_1 @ X31 @ X32 @ X33))
% 0.40/0.58            = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.40/0.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.40/0.58      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.40/0.58         = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.58  thf('63', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('64', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.40/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.58  thf('65', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.40/0.58  thf('66', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.40/0.58         = (k1_relat_1 @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['62', '65'])).
% 0.40/0.58  thf('67', plain, (((k1_xboole_0) = (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('68', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0) = (k1_relat_1 @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.40/0.58  thf('69', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup+', [status(thm)], ['59', '68'])).
% 0.40/0.58  thf('70', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) != (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('71', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.40/0.58  thf('72', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['70', '71'])).
% 0.40/0.58  thf('73', plain, ($false),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['69', '72'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
