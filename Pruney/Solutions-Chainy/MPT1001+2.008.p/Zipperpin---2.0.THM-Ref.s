%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2JfPDeNPyO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 151 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  814 (1999 expanded)
%              Number of equality atoms :   71 ( 148 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t49_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) )
                = k1_xboole_0 ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) )
                  = k1_xboole_0 ) )
        <=> ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_funct_2])).

thf('0',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(t143_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                = k1_xboole_0 ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C @ X12 @ X13 ) @ X13 )
      | ( r1_tarski @ X13 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_funct_1])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k1_tarski @ ( sk_C @ X12 @ X13 ) ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X13 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_funct_1])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X24: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ~ ! [X24: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X24 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
   <= ( r2_hidden @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('44',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('47',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X10 ) )
      | ( ( k10_relat_1 @ X10 @ ( k1_tarski @ X11 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_D @ sk_B ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','39','41','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2JfPDeNPyO
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 66 iterations in 0.028s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(t49_funct_2, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.47       ( ( ![D:$i]:
% 0.20/0.47           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.47                ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.47                  ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.47         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.47            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.47          ( ( ![D:$i]:
% 0.20/0.47              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.47                   ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.47                     ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.47            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t49_funct_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.47        | (r2_hidden @ sk_D @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (((r2_hidden @ sk_D @ sk_B)) | 
% 0.20/0.47       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X24 : $i]:
% 0.20/0.47         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 0.20/0.47          | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47              != (k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X24 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((![X24 : $i]:
% 0.20/0.47          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47             != (k1_xboole_0))
% 0.20/0.47           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 0.20/0.47       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf(t143_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( ![C:$i]:
% 0.20/0.47           ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.47                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.20/0.47         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C @ X12 @ X13) @ X13)
% 0.20/0.47          | (r1_tarski @ X13 @ (k2_relat_1 @ X12))
% 0.20/0.47          | ~ (v1_relat_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (((k10_relat_1 @ X12 @ (k1_tarski @ (sk_C @ X12 @ X13)))
% 0.20/0.47            = (k1_xboole_0))
% 0.20/0.47          | (r1_tarski @ X13 @ (k2_relat_1 @ X12))
% 0.20/0.47          | ~ (v1_relat_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.47          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.47           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((![X24 : $i]:
% 0.20/0.47          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47             != (k1_xboole_0))
% 0.20/0.47           | ~ (r2_hidden @ X24 @ sk_B)))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.20/0.47           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47           | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.47           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.47           | ~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.47          | (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf(fc6_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.47  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.47           | ~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)
% 0.20/0.47           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.47         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.47         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '18'])).
% 0.20/0.47  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.47         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         ((v5_relat_1 @ X14 @ X16)
% 0.20/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.47  thf('25', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf(d19_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (v5_relat_1 @ X6 @ X7)
% 0.20/0.47          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.20/0.47          | ~ (v1_relat_1 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('29', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.47        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 0.20/0.47         <= ((![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.47         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.20/0.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 0.20/0.47         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 0.20/0.47         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((((sk_B) != (sk_B)))
% 0.20/0.47         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.47             (![X24 : $i]:
% 0.20/0.47                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47                   != (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['32', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (~
% 0.20/0.47       (![X24 : $i]:
% 0.20/0.47          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X24))
% 0.20/0.47             != (k1_xboole_0))
% 0.20/0.47           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 0.20/0.47       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.47        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47            = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47          = (k1_xboole_0))) | 
% 0.20/0.47       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (((r2_hidden @ sk_D @ sk_B)) <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.47           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47          = (k1_xboole_0)))
% 0.20/0.47         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47                = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['40'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      ((((k10_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D)) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47                = (k1_xboole_0))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 0.20/0.47         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 0.20/0.47         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.47  thf(t142_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.47         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X11 @ (k2_relat_1 @ X10))
% 0.20/0.47          | ((k10_relat_1 @ X10 @ (k1_tarski @ X11)) != (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.47           | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.47           | ((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.20/0.47         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.47  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.47           | ((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.20/0.47         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.47      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_D @ sk_B)))
% 0.20/0.47         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.47             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47                = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['45', '52'])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      ((~ (r2_hidden @ sk_D @ sk_B))
% 0.20/0.47         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.47             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47                = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.47          = (k1_xboole_0))) | 
% 0.20/0.47       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 0.20/0.47       ~ ((r2_hidden @ sk_D @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '54'])).
% 0.20/0.47  thf('56', plain, ($false),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['1', '3', '39', '41', '55'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
