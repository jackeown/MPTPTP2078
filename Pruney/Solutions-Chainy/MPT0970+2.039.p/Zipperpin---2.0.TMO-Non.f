%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aXmfOXyyph

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:22 EST 2020

% Result     : Timeout 58.41s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   99 ( 334 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :   23
%              Number of atoms          :  875 (5060 expanded)
%              Number of equality atoms :   53 ( 345 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( ( k9_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ ( sk_C @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('14',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ( X28
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ( X0 = sk_B )
      | ( ( sk_C @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('17',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X28 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ( X0 = sk_B )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X27 @ X24 ) @ ( k2_relset_1 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( X0 = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ( X0 = sk_B ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ X0 )
      | ( X0 = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('34',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) ) @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('55',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) ) @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('58',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) ) @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('61',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aXmfOXyyph
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:43:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 58.41/58.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 58.41/58.60  % Solved by: fo/fo7.sh
% 58.41/58.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 58.41/58.60  % done 5176 iterations in 58.139s
% 58.41/58.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 58.41/58.60  % SZS output start Refutation
% 58.41/58.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 58.41/58.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 58.41/58.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 58.41/58.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 58.41/58.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 58.41/58.60  thf(sk_E_type, type, sk_E: $i > $i).
% 58.41/58.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 58.41/58.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 58.41/58.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 58.41/58.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 58.41/58.60  thf(sk_B_type, type, sk_B: $i).
% 58.41/58.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 58.41/58.60  thf(sk_A_type, type, sk_A: $i).
% 58.41/58.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 58.41/58.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 58.41/58.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 58.41/58.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 58.41/58.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 58.41/58.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 58.41/58.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 58.41/58.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 58.41/58.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 58.41/58.60  thf('0', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 58.41/58.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 58.41/58.60  thf(t2_tarski, axiom,
% 58.41/58.60    (![A:$i,B:$i]:
% 58.41/58.60     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 58.41/58.60       ( ( A ) = ( B ) ) ))).
% 58.41/58.60  thf('1', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         (((X1) = (X0))
% 58.41/58.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 58.41/58.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 58.41/58.60      inference('cnf', [status(esa)], [t2_tarski])).
% 58.41/58.60  thf(t7_ordinal1, axiom,
% 58.41/58.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 58.41/58.60  thf('2', plain,
% 58.41/58.60      (![X16 : $i, X17 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 58.41/58.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 58.41/58.60  thf('3', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 58.41/58.60          | ((X0) = (X1))
% 58.41/58.60          | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 58.41/58.60      inference('sup-', [status(thm)], ['1', '2'])).
% 58.41/58.60  thf('4', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 58.41/58.60      inference('sup-', [status(thm)], ['0', '3'])).
% 58.41/58.60  thf(t146_relat_1, axiom,
% 58.41/58.60    (![A:$i]:
% 58.41/58.60     ( ( v1_relat_1 @ A ) =>
% 58.41/58.60       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 58.41/58.60  thf('5', plain,
% 58.41/58.60      (![X15 : $i]:
% 58.41/58.60         (((k9_relat_1 @ X15 @ (k1_relat_1 @ X15)) = (k2_relat_1 @ X15))
% 58.41/58.60          | ~ (v1_relat_1 @ X15))),
% 58.41/58.60      inference('cnf', [status(esa)], [t146_relat_1])).
% 58.41/58.60  thf(t143_relat_1, axiom,
% 58.41/58.60    (![A:$i,B:$i,C:$i]:
% 58.41/58.60     ( ( v1_relat_1 @ C ) =>
% 58.41/58.60       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 58.41/58.60         ( ?[D:$i]:
% 58.41/58.60           ( ( r2_hidden @ D @ B ) & 
% 58.41/58.60             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 58.41/58.60             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 58.41/58.60  thf('6', plain,
% 58.41/58.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 58.41/58.60          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 58.41/58.60          | ~ (v1_relat_1 @ X14))),
% 58.41/58.60      inference('cnf', [status(esa)], [t143_relat_1])).
% 58.41/58.60  thf('7', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 58.41/58.60          | ~ (v1_relat_1 @ X0)
% 58.41/58.60          | ~ (v1_relat_1 @ X0)
% 58.41/58.60          | (r2_hidden @ 
% 58.41/58.60             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 58.41/58.60      inference('sup-', [status(thm)], ['5', '6'])).
% 58.41/58.60  thf('8', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         ((r2_hidden @ 
% 58.41/58.60           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 58.41/58.60          | ~ (v1_relat_1 @ X0)
% 58.41/58.60          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 58.41/58.60      inference('simplify', [status(thm)], ['7'])).
% 58.41/58.60  thf('9', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         (((k1_xboole_0) = (k2_relat_1 @ X0))
% 58.41/58.60          | ~ (v1_relat_1 @ X0)
% 58.41/58.60          | (r2_hidden @ 
% 58.41/58.60             (k4_tarski @ 
% 58.41/58.60              (sk_D @ X0 @ (k1_relat_1 @ X0) @ 
% 58.41/58.60               (sk_C @ (k2_relat_1 @ X0) @ k1_xboole_0)) @ 
% 58.41/58.60              (sk_C @ (k2_relat_1 @ X0) @ k1_xboole_0)) @ 
% 58.41/58.60             X0))),
% 58.41/58.60      inference('sup-', [status(thm)], ['4', '8'])).
% 58.41/58.60  thf(t16_funct_2, conjecture,
% 58.41/58.60    (![A:$i,B:$i,C:$i]:
% 58.41/58.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 58.41/58.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 58.41/58.60       ( ( ![D:$i]:
% 58.41/58.60           ( ~( ( r2_hidden @ D @ B ) & 
% 58.41/58.60                ( ![E:$i]:
% 58.41/58.60                  ( ~( ( r2_hidden @ E @ A ) & 
% 58.41/58.60                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 58.41/58.60         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 58.41/58.60  thf(zf_stmt_0, negated_conjecture,
% 58.41/58.60    (~( ![A:$i,B:$i,C:$i]:
% 58.41/58.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 58.41/58.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 58.41/58.60          ( ( ![D:$i]:
% 58.41/58.60              ( ~( ( r2_hidden @ D @ B ) & 
% 58.41/58.60                   ( ![E:$i]:
% 58.41/58.60                     ( ~( ( r2_hidden @ E @ A ) & 
% 58.41/58.60                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 58.41/58.60            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 58.41/58.60    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 58.41/58.60  thf('10', plain,
% 58.41/58.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf(l3_subset_1, axiom,
% 58.41/58.60    (![A:$i,B:$i]:
% 58.41/58.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 58.41/58.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 58.41/58.60  thf('11', plain,
% 58.41/58.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X8 @ X9)
% 58.41/58.60          | (r2_hidden @ X8 @ X10)
% 58.41/58.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 58.41/58.60      inference('cnf', [status(esa)], [l3_subset_1])).
% 58.41/58.60  thf('12', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.41/58.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 58.41/58.60      inference('sup-', [status(thm)], ['10', '11'])).
% 58.41/58.60  thf('13', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         (((X1) = (X0))
% 58.41/58.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 58.41/58.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 58.41/58.60      inference('cnf', [status(esa)], [t2_tarski])).
% 58.41/58.60  thf('14', plain,
% 58.41/58.60      (![X28 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X28 @ sk_B)
% 58.41/58.60          | ((X28) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X28))))),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf('15', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ (sk_C @ sk_B @ X0) @ X0)
% 58.41/58.60          | ((X0) = (sk_B))
% 58.41/58.60          | ((sk_C @ sk_B @ X0)
% 58.41/58.60              = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ sk_B @ X0)))))),
% 58.41/58.60      inference('sup-', [status(thm)], ['13', '14'])).
% 58.41/58.60  thf('16', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         (((X1) = (X0))
% 58.41/58.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 58.41/58.60          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 58.41/58.60      inference('cnf', [status(esa)], [t2_tarski])).
% 58.41/58.60  thf('17', plain,
% 58.41/58.60      (![X28 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X28 @ sk_B) | (r2_hidden @ (sk_E @ X28) @ sk_A))),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf('18', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ (sk_C @ sk_B @ X0) @ X0)
% 58.41/58.60          | ((X0) = (sk_B))
% 58.41/58.60          | (r2_hidden @ (sk_E @ (sk_C @ sk_B @ X0)) @ sk_A))),
% 58.41/58.60      inference('sup-', [status(thm)], ['16', '17'])).
% 58.41/58.60  thf('19', plain,
% 58.41/58.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf(t6_funct_2, axiom,
% 58.41/58.60    (![A:$i,B:$i,C:$i,D:$i]:
% 58.41/58.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 58.41/58.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 58.41/58.60       ( ( r2_hidden @ C @ A ) =>
% 58.41/58.60         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 58.41/58.60           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 58.41/58.60  thf('20', plain,
% 58.41/58.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X24 @ X25)
% 58.41/58.60          | ((X26) = (k1_xboole_0))
% 58.41/58.60          | ~ (v1_funct_1 @ X27)
% 58.41/58.60          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 58.41/58.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 58.41/58.60          | (r2_hidden @ (k1_funct_1 @ X27 @ X24) @ 
% 58.41/58.60             (k2_relset_1 @ X25 @ X26 @ X27)))),
% 58.41/58.60      inference('cnf', [status(esa)], [t6_funct_2])).
% 58.41/58.60  thf('21', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 58.41/58.60           (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 58.41/58.60          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 58.41/58.60          | ~ (v1_funct_1 @ sk_C_1)
% 58.41/58.60          | ((sk_B) = (k1_xboole_0))
% 58.41/58.60          | ~ (r2_hidden @ X0 @ sk_A))),
% 58.41/58.60      inference('sup-', [status(thm)], ['19', '20'])).
% 58.41/58.60  thf('22', plain,
% 58.41/58.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf(redefinition_k2_relset_1, axiom,
% 58.41/58.60    (![A:$i,B:$i,C:$i]:
% 58.41/58.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 58.41/58.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 58.41/58.60  thf('23', plain,
% 58.41/58.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 58.41/58.60         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 58.41/58.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 58.41/58.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 58.41/58.60  thf('24', plain,
% 58.41/58.60      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 58.41/58.60      inference('sup-', [status(thm)], ['22', '23'])).
% 58.41/58.60  thf('25', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf('26', plain, ((v1_funct_1 @ sk_C_1)),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf('27', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 58.41/58.60          | ((sk_B) = (k1_xboole_0))
% 58.41/58.60          | ~ (r2_hidden @ X0 @ sk_A))),
% 58.41/58.60      inference('demod', [status(thm)], ['21', '24', '25', '26'])).
% 58.41/58.60  thf('28', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         (((X0) = (sk_B))
% 58.41/58.60          | (r2_hidden @ (sk_C @ sk_B @ X0) @ X0)
% 58.41/58.60          | ((sk_B) = (k1_xboole_0))
% 58.41/58.60          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ sk_B @ X0))) @ 
% 58.41/58.60             (k2_relat_1 @ sk_C_1)))),
% 58.41/58.60      inference('sup-', [status(thm)], ['18', '27'])).
% 58.41/58.60  thf('29', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ (sk_C @ sk_B @ X0) @ (k2_relat_1 @ sk_C_1))
% 58.41/58.60          | ((X0) = (sk_B))
% 58.41/58.60          | (r2_hidden @ (sk_C @ sk_B @ X0) @ X0)
% 58.41/58.60          | ((sk_B) = (k1_xboole_0))
% 58.41/58.60          | (r2_hidden @ (sk_C @ sk_B @ X0) @ X0)
% 58.41/58.60          | ((X0) = (sk_B)))),
% 58.41/58.60      inference('sup+', [status(thm)], ['15', '28'])).
% 58.41/58.60  thf('30', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         (((sk_B) = (k1_xboole_0))
% 58.41/58.60          | (r2_hidden @ (sk_C @ sk_B @ X0) @ X0)
% 58.41/58.60          | ((X0) = (sk_B))
% 58.41/58.60          | (r2_hidden @ (sk_C @ sk_B @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 58.41/58.60      inference('simplify', [status(thm)], ['29'])).
% 58.41/58.60  thf('31', plain,
% 58.41/58.60      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 58.41/58.60        | (r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 58.41/58.60           (k2_relat_1 @ sk_C_1))
% 58.41/58.60        | ((sk_B) = (k1_xboole_0)))),
% 58.41/58.60      inference('eq_fact', [status(thm)], ['30'])).
% 58.41/58.60  thf('32', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf('33', plain,
% 58.41/58.60      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 58.41/58.60      inference('sup-', [status(thm)], ['22', '23'])).
% 58.41/58.60  thf('34', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 58.41/58.60      inference('demod', [status(thm)], ['32', '33'])).
% 58.41/58.60  thf('35', plain,
% 58.41/58.60      (((r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 58.41/58.60         (k2_relat_1 @ sk_C_1))
% 58.41/58.60        | ((sk_B) = (k1_xboole_0)))),
% 58.41/58.60      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 58.41/58.60  thf('36', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         ((r2_hidden @ 
% 58.41/58.60           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 58.41/58.60          | ~ (v1_relat_1 @ X0)
% 58.41/58.60          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 58.41/58.60      inference('simplify', [status(thm)], ['7'])).
% 58.41/58.60  thf('37', plain,
% 58.41/58.60      ((((sk_B) = (k1_xboole_0))
% 58.41/58.60        | ~ (v1_relat_1 @ sk_C_1)
% 58.41/58.60        | (r2_hidden @ 
% 58.41/58.60           (k4_tarski @ 
% 58.41/58.60            (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 58.41/58.60             (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 58.41/58.60            (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 58.41/58.60           sk_C_1))),
% 58.41/58.60      inference('sup-', [status(thm)], ['35', '36'])).
% 58.41/58.60  thf('38', plain,
% 58.41/58.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.41/58.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.41/58.60  thf(cc1_relset_1, axiom,
% 58.41/58.60    (![A:$i,B:$i,C:$i]:
% 58.41/58.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 58.41/58.60       ( v1_relat_1 @ C ) ))).
% 58.41/58.60  thf('39', plain,
% 58.41/58.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 58.41/58.60         ((v1_relat_1 @ X18)
% 58.41/58.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 58.41/58.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 58.41/58.60  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 58.41/58.60      inference('sup-', [status(thm)], ['38', '39'])).
% 58.41/58.60  thf('41', plain,
% 58.41/58.60      ((((sk_B) = (k1_xboole_0))
% 58.41/58.60        | (r2_hidden @ 
% 58.41/58.60           (k4_tarski @ 
% 58.41/58.60            (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 58.41/58.60             (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 58.41/58.60            (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 58.41/58.60           sk_C_1))),
% 58.41/58.60      inference('demod', [status(thm)], ['37', '40'])).
% 58.41/58.60  thf('42', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.41/58.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 58.41/58.60      inference('sup-', [status(thm)], ['10', '11'])).
% 58.41/58.60  thf('43', plain,
% 58.41/58.60      ((((sk_B) = (k1_xboole_0))
% 58.41/58.60        | (r2_hidden @ 
% 58.41/58.60           (k4_tarski @ 
% 58.41/58.60            (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 58.41/58.60             (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 58.41/58.60            (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 58.41/58.60           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.41/58.60      inference('sup-', [status(thm)], ['41', '42'])).
% 58.41/58.60  thf(l54_zfmisc_1, axiom,
% 58.41/58.60    (![A:$i,B:$i,C:$i,D:$i]:
% 58.41/58.60     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 58.41/58.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 58.41/58.60  thf('44', plain,
% 58.41/58.60      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 58.41/58.60         ((r2_hidden @ X5 @ X6)
% 58.41/58.60          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 58.41/58.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 58.41/58.60  thf('45', plain,
% 58.41/58.60      ((((sk_B) = (k1_xboole_0))
% 58.41/58.60        | (r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B))),
% 58.41/58.60      inference('sup-', [status(thm)], ['43', '44'])).
% 58.41/58.60  thf('46', plain,
% 58.41/58.60      (![X0 : $i, X1 : $i]:
% 58.41/58.60         (((X1) = (X0))
% 58.41/58.60          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 58.41/58.60          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 58.41/58.60      inference('cnf', [status(esa)], [t2_tarski])).
% 58.41/58.60  thf('47', plain,
% 58.41/58.60      ((((sk_B) = (k1_xboole_0))
% 58.41/58.60        | ~ (r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 58.41/58.60             (k2_relat_1 @ sk_C_1))
% 58.41/58.60        | ((k2_relat_1 @ sk_C_1) = (sk_B)))),
% 58.41/58.60      inference('sup-', [status(thm)], ['45', '46'])).
% 58.41/58.60  thf('48', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 58.41/58.60      inference('demod', [status(thm)], ['32', '33'])).
% 58.41/58.60  thf('49', plain,
% 58.41/58.60      ((((sk_B) = (k1_xboole_0))
% 58.41/58.60        | ~ (r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 58.41/58.60             (k2_relat_1 @ sk_C_1)))),
% 58.41/58.60      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 58.41/58.60  thf('50', plain,
% 58.41/58.60      (((r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 58.41/58.60         (k2_relat_1 @ sk_C_1))
% 58.41/58.60        | ((sk_B) = (k1_xboole_0)))),
% 58.41/58.60      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 58.41/58.60  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 58.41/58.60      inference('clc', [status(thm)], ['49', '50'])).
% 58.41/58.60  thf('52', plain,
% 58.41/58.60      (![X0 : $i]:
% 58.41/58.60         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 58.41/58.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 58.41/58.60      inference('demod', [status(thm)], ['12', '51'])).
% 58.41/58.60  thf('53', plain,
% 58.41/58.60      ((~ (v1_relat_1 @ sk_C_1)
% 58.41/58.60        | ((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 58.41/58.60        | (r2_hidden @ 
% 58.41/58.60           (k4_tarski @ 
% 58.41/58.60            (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 58.41/58.60             (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0)) @ 
% 58.41/58.60            (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0)) @ 
% 58.41/58.60           (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 58.41/58.60      inference('sup-', [status(thm)], ['9', '52'])).
% 58.41/58.60  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 58.41/58.60      inference('sup-', [status(thm)], ['38', '39'])).
% 58.41/58.60  thf('55', plain,
% 58.41/58.60      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 58.41/58.60        | (r2_hidden @ 
% 58.41/58.60           (k4_tarski @ 
% 58.41/58.60            (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 58.41/58.60             (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0)) @ 
% 58.41/58.60            (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0)) @ 
% 58.41/58.60           (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 58.41/58.60      inference('demod', [status(thm)], ['53', '54'])).
% 58.41/58.60  thf('56', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 58.41/58.60      inference('demod', [status(thm)], ['32', '33'])).
% 58.41/58.60  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 58.41/58.60      inference('clc', [status(thm)], ['49', '50'])).
% 58.41/58.60  thf('58', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 58.41/58.60      inference('demod', [status(thm)], ['56', '57'])).
% 58.41/58.60  thf('59', plain,
% 58.41/58.60      ((r2_hidden @ 
% 58.41/58.60        (k4_tarski @ 
% 58.41/58.60         (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 58.41/58.60          (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0)) @ 
% 58.41/58.60         (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0)) @ 
% 58.41/58.60        (k2_zfmisc_1 @ sk_A @ k1_xboole_0))),
% 58.41/58.60      inference('simplify_reflect-', [status(thm)], ['55', '58'])).
% 58.41/58.60  thf('60', plain,
% 58.41/58.60      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 58.41/58.60         ((r2_hidden @ X5 @ X6)
% 58.41/58.60          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 58.41/58.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 58.41/58.60  thf('61', plain,
% 58.41/58.60      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0) @ k1_xboole_0)),
% 58.41/58.60      inference('sup-', [status(thm)], ['59', '60'])).
% 58.41/58.60  thf('62', plain,
% 58.41/58.60      (![X16 : $i, X17 : $i]:
% 58.41/58.60         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 58.41/58.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 58.41/58.60  thf('63', plain,
% 58.41/58.60      (~ (r1_tarski @ k1_xboole_0 @ 
% 58.41/58.60          (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0))),
% 58.41/58.60      inference('sup-', [status(thm)], ['61', '62'])).
% 58.41/58.60  thf('64', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 58.41/58.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 58.41/58.60  thf('65', plain, ($false), inference('demod', [status(thm)], ['63', '64'])).
% 58.41/58.60  
% 58.41/58.60  % SZS output end Refutation
% 58.41/58.60  
% 58.44/58.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
