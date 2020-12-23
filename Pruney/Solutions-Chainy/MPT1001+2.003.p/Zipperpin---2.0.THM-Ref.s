%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWZwL3nTUN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 133 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  801 (1880 expanded)
%              Number of equality atoms :   71 ( 146 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X26: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k1_tarski @ X12 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X12 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_C @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('23',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X26: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X26: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X26 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ! [X26: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X26 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
   <= ( r2_hidden @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('42',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('45',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X11 ) )
      | ( ( k10_relat_1 @ X11 @ ( k1_tarski @ X12 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_D @ sk_B ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','37','39','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWZwL3nTUN
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 102 iterations in 0.048s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(t49_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( ![D:$i]:
% 0.21/0.50           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.50                ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.21/0.50                  ( k1_xboole_0 ) ) ) ) ) <=>
% 0.21/0.50         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.50            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50          ( ( ![D:$i]:
% 0.21/0.50              ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.50                   ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.21/0.50                     ( k1_xboole_0 ) ) ) ) ) <=>
% 0.21/0.50            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t49_funct_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.21/0.50        | (r2_hidden @ sk_D @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (((r2_hidden @ sk_D @ sk_B)) | 
% 0.21/0.50       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X26 : $i]:
% 0.21/0.50         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 0.21/0.50          | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50              != (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X26 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((![X26 : $i]:
% 0.21/0.50          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50             != (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X26 @ sk_B))) | 
% 0.21/0.50       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf(t142_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.50         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (((k10_relat_1 @ X11 @ (k1_tarski @ X12)) = (k1_xboole_0))
% 0.21/0.50          | (r2_hidden @ X12 @ (k2_relat_1 @ X11))
% 0.21/0.50          | ~ (v1_relat_1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((k10_relat_1 @ X0 @ (k1_tarski @ (sk_C @ (k2_relat_1 @ X0) @ X1)))
% 0.21/0.50              = (k1_xboole_0))
% 0.21/0.50          | (r1_tarski @ X1 @ (k2_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.50          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.21/0.50           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((![X26 : $i]:
% 0.21/0.50          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50             != (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X26 @ sk_B)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.21/0.50           | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.50           | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( v1_relat_1 @ C ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.21/0.50           | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B)
% 0.21/0.50           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.21/0.50         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k2_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '26'])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('29', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i]:
% 0.21/0.50         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.21/0.50        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 0.21/0.50         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 0.21/0.50         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((((sk_B) != (sk_B)))
% 0.21/0.50         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.21/0.50             (![X26 : $i]:
% 0.21/0.50                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50                   != (k1_xboole_0))
% 0.21/0.50                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (~
% 0.21/0.50       (![X26 : $i]:
% 0.21/0.50          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X26))
% 0.21/0.50             != (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X26 @ sk_B))) | 
% 0.21/0.50       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.21/0.50        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50            = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50          = (k1_xboole_0))) | 
% 0.21/0.50       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((r2_hidden @ sk_D @ sk_B)) <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.21/0.50           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50          = (k1_xboole_0)))
% 0.21/0.50         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50                = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['38'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D)) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50                = (k1_xboole_0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 0.21/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 0.21/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X12 @ (k2_relat_1 @ X11))
% 0.21/0.50          | ((k10_relat_1 @ X11 @ (k1_tarski @ X12)) != (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.50           | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.50           | ((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.21/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.50           | ((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))))
% 0.21/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_D @ sk_B)))
% 0.21/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.21/0.50             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50                = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_D @ sk_B))
% 0.21/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.21/0.50             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50                = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (~
% 0.21/0.50       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.21/0.50          = (k1_xboole_0))) | 
% 0.21/0.50       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 0.21/0.50       ~ ((r2_hidden @ sk_D @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '52'])).
% 0.21/0.50  thf('54', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['1', '3', '37', '39', '53'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
