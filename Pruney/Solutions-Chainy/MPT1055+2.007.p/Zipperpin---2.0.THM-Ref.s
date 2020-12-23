%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.STTXbWFA5p

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:34 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 167 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  886 (2721 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t172_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                     => ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E )
                      <=> ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                       => ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E )
                        <=> ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t172_funct_2])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( ( k8_relset_1 @ X32 @ X34 @ X33 @ X34 )
        = X32 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('10',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k8_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k10_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13','14','15'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('27',plain,(
    r2_hidden @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['27','29'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X19 @ X18 ) @ X20 )
      | ( r1_tarski @ X18 @ ( k10_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C_1 @ sk_E ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['7','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C_1 @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      & ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      & ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ ( k10_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('50',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k9_relat_1 @ X13 @ X11 ) @ ( k9_relat_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('56',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C_1 @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('61',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.STTXbWFA5p
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.64/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.84  % Solved by: fo/fo7.sh
% 0.64/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.84  % done 571 iterations in 0.387s
% 0.64/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.84  % SZS output start Refutation
% 0.64/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.64/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.64/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.64/0.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.64/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.64/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.64/0.84  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.64/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.64/0.84  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.64/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.64/0.84  thf(sk_D_type, type, sk_D: $i).
% 0.64/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.64/0.84  thf(sk_E_type, type, sk_E: $i).
% 0.64/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.84  thf(t172_funct_2, conjecture,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.64/0.84           ( ![C:$i]:
% 0.64/0.84             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.64/0.84                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.64/0.84               ( ![D:$i]:
% 0.64/0.84                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.84                   ( ![E:$i]:
% 0.64/0.84                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.64/0.84                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.64/0.84                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.84    (~( ![A:$i]:
% 0.64/0.84        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.84          ( ![B:$i]:
% 0.64/0.84            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.64/0.84              ( ![C:$i]:
% 0.64/0.84                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.64/0.84                    ( m1_subset_1 @
% 0.64/0.84                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.64/0.84                  ( ![D:$i]:
% 0.64/0.84                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.84                      ( ![E:$i]:
% 0.64/0.84                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.64/0.84                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.64/0.84                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.64/0.84    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 0.64/0.84  thf('0', plain,
% 0.64/0.84      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))
% 0.64/0.84        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('1', plain,
% 0.64/0.84      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))) | 
% 0.64/0.84       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))),
% 0.64/0.84      inference('split', [status(esa)], ['0'])).
% 0.64/0.84  thf('2', plain,
% 0.64/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(redefinition_k7_relset_1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.84       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.64/0.84  thf('3', plain,
% 0.64/0.84      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.64/0.84          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.64/0.84      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.64/0.84  thf('4', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.64/0.84           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.64/0.84  thf('5', plain,
% 0.64/0.84      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))
% 0.64/0.84        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('6', plain,
% 0.64/0.84      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))
% 0.64/0.84         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E)))),
% 0.64/0.84      inference('split', [status(esa)], ['5'])).
% 0.64/0.84  thf('7', plain,
% 0.64/0.84      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E))
% 0.64/0.84         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E)))),
% 0.64/0.84      inference('sup+', [status(thm)], ['4', '6'])).
% 0.64/0.84  thf('8', plain,
% 0.64/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(t48_funct_2, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i]:
% 0.64/0.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.64/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.64/0.84       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.64/0.84         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.64/0.84  thf('9', plain,
% 0.64/0.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.64/0.84         (((X34) = (k1_xboole_0))
% 0.64/0.84          | ~ (v1_funct_1 @ X33)
% 0.64/0.84          | ~ (v1_funct_2 @ X33 @ X32 @ X34)
% 0.64/0.84          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 0.64/0.84          | ((k8_relset_1 @ X32 @ X34 @ X33 @ X34) = (X32)))),
% 0.64/0.84      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.64/0.84  thf('10', plain,
% 0.64/0.84      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B) = (sk_A))
% 0.64/0.84        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.64/0.84        | ~ (v1_funct_1 @ sk_C_1)
% 0.64/0.84        | ((sk_B) = (k1_xboole_0)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.64/0.84  thf('11', plain,
% 0.64/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(redefinition_k8_relset_1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.84       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.64/0.84  thf('12', plain,
% 0.64/0.84      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.64/0.84          | ((k8_relset_1 @ X29 @ X30 @ X28 @ X31) = (k10_relat_1 @ X28 @ X31)))),
% 0.64/0.84      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.64/0.84  thf('13', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.64/0.84           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.64/0.84  thf('14', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('16', plain,
% 0.64/0.84      ((((k10_relat_1 @ sk_C_1 @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.64/0.84      inference('demod', [status(thm)], ['10', '13', '14', '15'])).
% 0.64/0.84  thf(t167_relat_1, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( v1_relat_1 @ B ) =>
% 0.64/0.84       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.64/0.84  thf('17', plain,
% 0.64/0.84      (![X14 : $i, X15 : $i]:
% 0.64/0.84         ((r1_tarski @ (k10_relat_1 @ X14 @ X15) @ (k1_relat_1 @ X14))
% 0.64/0.84          | ~ (v1_relat_1 @ X14))),
% 0.64/0.84      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.64/0.84  thf('18', plain,
% 0.64/0.84      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.64/0.84        | ((sk_B) = (k1_xboole_0))
% 0.64/0.84        | ~ (v1_relat_1 @ sk_C_1))),
% 0.64/0.84      inference('sup+', [status(thm)], ['16', '17'])).
% 0.64/0.84  thf('19', plain,
% 0.64/0.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(cc1_relset_1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i]:
% 0.64/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.84       ( v1_relat_1 @ C ) ))).
% 0.64/0.84  thf('20', plain,
% 0.64/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.64/0.84         ((v1_relat_1 @ X21)
% 0.64/0.84          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.64/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.64/0.84  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.64/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.64/0.84  thf('22', plain,
% 0.64/0.84      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1)) | ((sk_B) = (k1_xboole_0)))),
% 0.64/0.84      inference('demod', [status(thm)], ['18', '21'])).
% 0.64/0.84  thf('23', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf(t2_subset, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( m1_subset_1 @ A @ B ) =>
% 0.64/0.84       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.64/0.84  thf('24', plain,
% 0.64/0.84      (![X9 : $i, X10 : $i]:
% 0.64/0.84         ((r2_hidden @ X9 @ X10)
% 0.64/0.84          | (v1_xboole_0 @ X10)
% 0.64/0.84          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.64/0.84      inference('cnf', [status(esa)], [t2_subset])).
% 0.64/0.84  thf('25', plain,
% 0.64/0.84      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.64/0.84        | (r2_hidden @ sk_D @ (k1_zfmisc_1 @ sk_A)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['23', '24'])).
% 0.64/0.84  thf(fc1_subset_1, axiom,
% 0.64/0.84    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.64/0.84  thf('26', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.64/0.84      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.64/0.84  thf('27', plain, ((r2_hidden @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.84      inference('clc', [status(thm)], ['25', '26'])).
% 0.64/0.84  thf(d1_zfmisc_1, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.64/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.64/0.84  thf('28', plain,
% 0.64/0.84      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.84         (~ (r2_hidden @ X6 @ X5)
% 0.64/0.84          | (r1_tarski @ X6 @ X4)
% 0.64/0.84          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.64/0.84      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.64/0.84  thf('29', plain,
% 0.64/0.84      (![X4 : $i, X6 : $i]:
% 0.64/0.84         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.64/0.84      inference('simplify', [status(thm)], ['28'])).
% 0.64/0.84  thf('30', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.64/0.84      inference('sup-', [status(thm)], ['27', '29'])).
% 0.64/0.84  thf(t1_xboole_1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i]:
% 0.64/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.64/0.84       ( r1_tarski @ A @ C ) ))).
% 0.64/0.84  thf('31', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.64/0.84          | ~ (r1_tarski @ X1 @ X2)
% 0.64/0.84          | (r1_tarski @ X0 @ X2))),
% 0.64/0.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.64/0.84  thf('32', plain,
% 0.64/0.84      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.64/0.84  thf('33', plain,
% 0.64/0.84      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C_1)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['22', '32'])).
% 0.64/0.84  thf(t163_funct_1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i]:
% 0.64/0.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.64/0.84       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.64/0.84           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.64/0.84         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.64/0.84  thf('34', plain,
% 0.64/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.64/0.84         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.64/0.84          | ~ (r1_tarski @ (k9_relat_1 @ X19 @ X18) @ X20)
% 0.64/0.84          | (r1_tarski @ X18 @ (k10_relat_1 @ X19 @ X20))
% 0.64/0.84          | ~ (v1_funct_1 @ X19)
% 0.64/0.84          | ~ (v1_relat_1 @ X19))),
% 0.64/0.84      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.64/0.84  thf('35', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         (((sk_B) = (k1_xboole_0))
% 0.64/0.84          | ~ (v1_relat_1 @ sk_C_1)
% 0.64/0.84          | ~ (v1_funct_1 @ sk_C_1)
% 0.64/0.84          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C_1 @ X0))
% 0.64/0.84          | ~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.64/0.84  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.64/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.64/0.84  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('38', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         (((sk_B) = (k1_xboole_0))
% 0.64/0.84          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C_1 @ X0))
% 0.64/0.84          | ~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ X0))),
% 0.64/0.84      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.64/0.84  thf('39', plain,
% 0.64/0.84      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C_1 @ sk_E))
% 0.64/0.84         | ((sk_B) = (k1_xboole_0))))
% 0.64/0.84         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['7', '38'])).
% 0.64/0.84  thf('40', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.64/0.84           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.64/0.84  thf('41', plain,
% 0.64/0.84      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E)))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('split', [status(esa)], ['0'])).
% 0.64/0.84  thf('42', plain,
% 0.64/0.84      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C_1 @ sk_E)))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.64/0.84  thf('43', plain,
% 0.64/0.84      ((((sk_B) = (k1_xboole_0)))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))) & 
% 0.64/0.84             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['39', '42'])).
% 0.64/0.84  thf('44', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('45', plain,
% 0.64/0.84      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))) & 
% 0.64/0.84             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.64/0.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.64/0.84  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.64/0.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.64/0.84  thf('47', plain,
% 0.64/0.84      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))) | 
% 0.64/0.84       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))),
% 0.64/0.84      inference('demod', [status(thm)], ['45', '46'])).
% 0.64/0.84  thf('48', plain,
% 0.64/0.84      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))) | 
% 0.64/0.84       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))),
% 0.64/0.84      inference('split', [status(esa)], ['5'])).
% 0.64/0.84  thf(t145_funct_1, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.64/0.84       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.64/0.84  thf('49', plain,
% 0.64/0.84      (![X16 : $i, X17 : $i]:
% 0.64/0.84         ((r1_tarski @ (k9_relat_1 @ X16 @ (k10_relat_1 @ X16 @ X17)) @ X17)
% 0.64/0.84          | ~ (v1_funct_1 @ X16)
% 0.64/0.84          | ~ (v1_relat_1 @ X16))),
% 0.64/0.84      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.64/0.84  thf('50', plain,
% 0.64/0.84      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E)))
% 0.64/0.84         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('split', [status(esa)], ['5'])).
% 0.64/0.84  thf(t156_relat_1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i]:
% 0.64/0.84     ( ( v1_relat_1 @ C ) =>
% 0.64/0.84       ( ( r1_tarski @ A @ B ) =>
% 0.64/0.84         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.64/0.84  thf('51', plain,
% 0.64/0.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.64/0.84         (~ (r1_tarski @ X11 @ X12)
% 0.64/0.84          | ~ (v1_relat_1 @ X13)
% 0.64/0.84          | (r1_tarski @ (k9_relat_1 @ X13 @ X11) @ (k9_relat_1 @ X13 @ X12)))),
% 0.64/0.84      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.64/0.84  thf('52', plain,
% 0.64/0.84      ((![X0 : $i]:
% 0.64/0.84          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.64/0.84            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E)))
% 0.64/0.84           | ~ (v1_relat_1 @ X0)))
% 0.64/0.84         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('sup-', [status(thm)], ['50', '51'])).
% 0.64/0.84  thf('53', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.64/0.84          | ~ (r1_tarski @ X1 @ X2)
% 0.64/0.84          | (r1_tarski @ X0 @ X2))),
% 0.64/0.84      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.64/0.84  thf('54', plain,
% 0.64/0.84      ((![X0 : $i, X1 : $i]:
% 0.64/0.84          (~ (v1_relat_1 @ X0)
% 0.64/0.84           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 0.64/0.84           | ~ (r1_tarski @ 
% 0.64/0.84                (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E)) @ 
% 0.64/0.84                X1)))
% 0.64/0.84         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('sup-', [status(thm)], ['52', '53'])).
% 0.64/0.84  thf('55', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.64/0.84           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.64/0.84  thf('56', plain,
% 0.64/0.84      ((![X0 : $i, X1 : $i]:
% 0.64/0.84          (~ (v1_relat_1 @ X0)
% 0.64/0.84           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 0.64/0.84           | ~ (r1_tarski @ 
% 0.64/0.84                (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C_1 @ sk_E)) @ X1)))
% 0.64/0.84         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('demod', [status(thm)], ['54', '55'])).
% 0.64/0.84  thf('57', plain,
% 0.64/0.84      (((~ (v1_relat_1 @ sk_C_1)
% 0.64/0.84         | ~ (v1_funct_1 @ sk_C_1)
% 0.64/0.84         | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E)
% 0.64/0.84         | ~ (v1_relat_1 @ sk_C_1)))
% 0.64/0.84         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('sup-', [status(thm)], ['49', '56'])).
% 0.64/0.84  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 0.64/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.64/0.84  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.84  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 0.64/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.64/0.84  thf('61', plain,
% 0.64/0.84      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E))
% 0.64/0.84         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))))),
% 0.64/0.84      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.64/0.84  thf('62', plain,
% 0.64/0.84      (![X0 : $i]:
% 0.64/0.84         ((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.64/0.84           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.64/0.84  thf('63', plain,
% 0.64/0.84      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E)))),
% 0.64/0.84      inference('split', [status(esa)], ['0'])).
% 0.64/0.84  thf('64', plain,
% 0.64/0.84      ((~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E))
% 0.64/0.84         <= (~
% 0.64/0.84             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E)))),
% 0.64/0.84      inference('sup-', [status(thm)], ['62', '63'])).
% 0.64/0.84  thf('65', plain,
% 0.64/0.84      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E))) | 
% 0.64/0.84       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_E))),
% 0.64/0.84      inference('sup-', [status(thm)], ['61', '64'])).
% 0.64/0.84  thf('66', plain, ($false),
% 0.64/0.84      inference('sat_resolution*', [status(thm)], ['1', '47', '48', '65'])).
% 0.64/0.84  
% 0.64/0.84  % SZS output end Refutation
% 0.64/0.84  
% 0.64/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
