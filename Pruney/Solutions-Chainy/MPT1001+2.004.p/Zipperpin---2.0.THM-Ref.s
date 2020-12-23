%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Ix5nlgLCo

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 151 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  915 (2068 expanded)
%              Number of equality atoms :   76 ( 155 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X31: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
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
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ( r1_tarski @ X17 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_funct_1])).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k1_tarski @ ( sk_C @ X16 @ X17 ) ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X17 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
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
      & ! [X31: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X31 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ! [X31: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ X31 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X31 @ sk_B ) )
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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('41',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ sk_B )
   <= ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('44',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('47',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('48',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('50',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('52',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_D ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','53'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('56',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ sk_D ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_D ) @ sk_B ) )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('59',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_D ) @ sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['42','60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','37','39','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Ix5nlgLCo
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 102 iterations in 0.042s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(t49_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ( ![D:$i]:
% 0.20/0.49           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.49                ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.49                  ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.49         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49          ( ( ![D:$i]:
% 0.20/0.49              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.49                   ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.49                     ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.49            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t49_funct_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.49        | (r2_hidden @ sk_D @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ sk_B)) | 
% 0.20/0.49       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X31 : $i]:
% 0.20/0.49         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 0.20/0.49          | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49              != (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X31 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((![X31 : $i]:
% 0.20/0.49          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49             != (k1_xboole_0))
% 0.20/0.49           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.20/0.49       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf(t143_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( ![C:$i]:
% 0.20/0.49           ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.49                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.20/0.49         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C @ X16 @ X17) @ X17)
% 0.20/0.49          | (r1_tarski @ X17 @ (k2_relat_1 @ X16))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X16 @ (k1_tarski @ (sk_C @ X16 @ X17)))
% 0.20/0.49            = (k1_xboole_0))
% 0.20/0.49          | (r1_tarski @ X17 @ (k2_relat_1 @ X16))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.20/0.49          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.49           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((![X31 : $i]:
% 0.20/0.49          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49             != (k1_xboole_0))
% 0.20/0.49           | ~ (r2_hidden @ X31 @ sk_B)))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((k10_relat_1 @ sk_C_1 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49           | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.49           | ~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( v1_relat_1 @ C ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X18)
% 0.20/0.49          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.49  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.49           | ~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)
% 0.20/0.49           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.49         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '16'])).
% 0.20/0.49  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.49         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.20/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.20/0.49        (k1_zfmisc_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.20/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('29', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X2 : $i, X4 : $i]:
% 0.20/0.49         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.20/0.49        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 0.20/0.49         <= ((![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 0.20/0.49         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 0.20/0.49         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((((sk_B) != (sk_B)))
% 0.20/0.49         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.49             (![X31 : $i]:
% 0.20/0.49                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49                   != (k1_xboole_0))
% 0.20/0.49                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (~
% 0.20/0.49       (![X31 : $i]:
% 0.20/0.49          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ X31))
% 0.20/0.49             != (k1_xboole_0))
% 0.20/0.49           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.20/0.49       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.49        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49            = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49          = (k1_xboole_0))) | 
% 0.20/0.49       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ sk_B)) <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(l1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X8 : $i, X10 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((r1_tarski @ (k1_tarski @ sk_D) @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 0.20/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 0.20/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.49           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49          = (k1_xboole_0)))
% 0.20/0.49         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['38'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D)) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf(t173_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 0.20/0.49          | (r1_xboole_0 @ (k2_relat_1 @ X14) @ X15)
% 0.20/0.49          | ~ (v1_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49         | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.49         | (r1_xboole_0 @ (k2_relat_1 @ sk_C_1) @ (k1_tarski @ sk_D))))
% 0.20/0.49         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49         | (r1_xboole_0 @ (k2_relat_1 @ sk_C_1) @ (k1_tarski @ sk_D))))
% 0.20/0.49         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((r1_xboole_0 @ (k2_relat_1 @ sk_C_1) @ (k1_tarski @ sk_D)))
% 0.20/0.49         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))
% 0.20/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.49             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['45', '53'])).
% 0.20/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B))
% 0.20/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.49             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf(t69_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X5 @ X6)
% 0.20/0.49          | ~ (r1_tarski @ X5 @ X6)
% 0.20/0.49          | (v1_xboole_0 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((((v1_xboole_0 @ (k1_tarski @ sk_D))
% 0.20/0.49         | ~ (r1_tarski @ (k1_tarski @ sk_D) @ sk_B)))
% 0.20/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.49             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.20/0.49  thf('59', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k1_tarski @ sk_D) @ sk_B))
% 0.20/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.49             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49                = (k1_xboole_0))))),
% 0.20/0.49      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.49          = (k1_xboole_0))) | 
% 0.20/0.49       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 0.20/0.49       ~ ((r2_hidden @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '60'])).
% 0.20/0.49  thf('62', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['1', '3', '37', '39', '61'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
