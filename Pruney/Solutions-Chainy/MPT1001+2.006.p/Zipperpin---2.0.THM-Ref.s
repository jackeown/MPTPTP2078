%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bSqzKvB7OM

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 281 expanded)
%              Number of leaves         :   34 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          : 1064 (4098 expanded)
%              Number of equality atoms :   93 ( 315 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
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
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ X15 )
      | ( r1_tarski @ X15 @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_funct_1])).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ ( k1_tarski @ ( sk_C_1 @ X14 @ X15 ) ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X15 @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_funct_1])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_C_2 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ sk_B )
        | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

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
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
   <= ! [X31: $i] :
        ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      & ! [X31: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X31 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ! [X31: $i] :
          ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ X31 ) )
           != k1_xboole_0 )
          | ~ ( r2_hidden @ X31 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0 )
      = ( k10_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('41',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('42',plain,
    ( ( ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
   <= ( r2_hidden @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('45',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ sk_B )
   <= ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('47',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ~ ( v1_relat_1 @ sk_C_2 )
        | ~ ( v1_funct_1 @ sk_C_2 )
        | ( ( k9_relat_1 @ sk_C_2 @ ( k10_relat_1 @ sk_C_2 @ X0 ) )
          = X0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( ( k9_relat_1 @ sk_C_2 @ ( k10_relat_1 @ sk_C_2 @ X0 ) )
          = X0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( k9_relat_1 @ sk_C_2 @ ( k10_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_D ) ) )
      = ( k1_tarski @ sk_D ) )
   <= ( ( r2_hidden @ sk_D @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( k9_relat_1 @ sk_C_2 @ k1_xboole_0 )
      = ( k1_tarski @ sk_D ) )
   <= ( ( r2_hidden @ sk_D @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','54'])).

thf(t171_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('56',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t171_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( ( k9_relat_1 @ sk_C_2 @ ( k10_relat_1 @ sk_C_2 @ X0 ) )
          = X0 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_C_2 @ ( k10_relat_1 @ sk_C_2 @ k1_xboole_0 ) )
      = k1_xboole_0 )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( ( k9_relat_1 @ sk_C_2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_2 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('62',plain,
    ( ( ( k9_relat_1 @ sk_C_2 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_D @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( r2_hidden @ sk_D @ X0 ) )
   <= ( ( r2_hidden @ sk_D @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_D @ X0 )
   <= ( ( r2_hidden @ sk_D @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( sk_C @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_D @ X0 )
   <= ( ( r2_hidden @ sk_D @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_D @ X0 )
   <= ( ( r2_hidden @ sk_D @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      & ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('72',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','37','39','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bSqzKvB7OM
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 141 iterations in 0.054s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(t49_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ( ![D:$i]:
% 0.20/0.51           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.51                ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.51                  ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.51         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51          ( ( ![D:$i]:
% 0.20/0.51              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.51                   ( ( k8_relset_1 @ A @ B @ C @ ( k1_tarski @ D ) ) =
% 0.20/0.51                     ( k1_xboole_0 ) ) ) ) ) <=>
% 0.20/0.51            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t49_funct_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.20/0.51        | (r2_hidden @ sk_D @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r2_hidden @ sk_D @ sk_B)) | 
% 0.20/0.51       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X31 : $i]:
% 0.20/0.51         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 0.20/0.51          | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51              != (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X31 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((![X31 : $i]:
% 0.20/0.51          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51             != (k1_xboole_0))
% 0.20/0.51           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.20/0.51       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf(t143_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( ![C:$i]:
% 0.20/0.51           ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.51                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.20/0.51         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C_1 @ X14 @ X15) @ X15)
% 0.20/0.51          | (r1_tarski @ X15 @ (k2_relat_1 @ X14))
% 0.20/0.51          | ~ (v1_relat_1 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X14 @ (k1_tarski @ (sk_C_1 @ X14 @ X15)))
% 0.20/0.51            = (k1_xboole_0))
% 0.20/0.51          | (r1_tarski @ X15 @ (k2_relat_1 @ X14))
% 0.20/0.51          | ~ (v1_relat_1 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t143_funct_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.20/0.51          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.20/0.51           = (k10_relat_1 @ sk_C_2 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((![X31 : $i]:
% 0.20/0.51          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51             != (k1_xboole_0))
% 0.20/0.51           | ~ (r2_hidden @ X31 @ sk_B)))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k10_relat_1 @ sk_C_2 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51           | ~ (v1_relat_1 @ sk_C_2)
% 0.20/0.51           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.20/0.51           | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ sk_B)))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( v1_relat_1 @ C ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X18)
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('14', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.20/0.51           | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ sk_B)))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ sk_B)
% 0.20/0.51           | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2))))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_C_2)
% 0.20/0.51         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.20/0.51         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '16'])).
% 0.20/0.51  thf('18', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.20/0.51         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.20/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.20/0.51        (k1_zfmisc_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('29', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.20/0.51        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((sk_B) = (k2_relat_1 @ sk_C_2)))
% 0.20/0.51         <= ((![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B)))
% 0.20/0.51         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) != (sk_B)))
% 0.20/0.51         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((((sk_B) != (sk_B)))
% 0.20/0.51         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (![X31 : $i]:
% 0.20/0.51                (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51                   != (k1_xboole_0))
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (~
% 0.20/0.51       (![X31 : $i]:
% 0.20/0.51          (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ X31))
% 0.20/0.51             != (k1_xboole_0))
% 0.20/0.51           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.20/0.51       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.20/0.51        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51            = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51          = (k1_xboole_0))) | 
% 0.20/0.51       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.20/0.51           = (k10_relat_1 @ sk_C_2 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51          = (k1_xboole_0)))
% 0.20/0.51         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['38'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D)) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((r2_hidden @ sk_D @ sk_B)) <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(t37_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((r1_tarski @ (k1_tarski @ sk_D) @ sk_B))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf(t147_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.51         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.20/0.51          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.20/0.51          | ~ (v1_funct_1 @ X17)
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.51           | ~ (v1_relat_1 @ sk_C_2)
% 0.20/0.51           | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.51           | ((k9_relat_1 @ sk_C_2 @ (k10_relat_1 @ sk_C_2 @ X0)) = (X0))))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('52', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.51           | ((k9_relat_1 @ sk_C_2 @ (k10_relat_1 @ sk_C_2 @ X0)) = (X0))))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((((k9_relat_1 @ sk_C_2 @ (k10_relat_1 @ sk_C_2 @ (k1_tarski @ sk_D)))
% 0.20/0.51          = (k1_tarski @ sk_D)))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((((k9_relat_1 @ sk_C_2 @ k1_xboole_0) = (k1_tarski @ sk_D)))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['42', '54'])).
% 0.20/0.51  thf(t171_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X13 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t171_relat_1])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('57', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.51           | ((k9_relat_1 @ sk_C_2 @ (k10_relat_1 @ sk_C_2 @ X0)) = (X0))))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((((k9_relat_1 @ sk_C_2 @ (k10_relat_1 @ sk_C_2 @ k1_xboole_0))
% 0.20/0.51          = (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (((((k9_relat_1 @ sk_C_2 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.51         | ~ (v1_relat_1 @ sk_C_2)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['56', '59'])).
% 0.20/0.51  thf('61', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      ((((k9_relat_1 @ sk_C_2 @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['55', '62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         ((r2_hidden @ X4 @ X5) | ~ (r1_tarski @ (k1_tarski @ X4) @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_D @ X0)))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.51  thf('66', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((![X0 : $i]: (r2_hidden @ sk_D @ X0))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf(t7_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( r2_hidden @ A @ B ) & 
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.51          | ~ (r2_hidden @ X9 @ X8)
% 0.20/0.51          | ~ (r2_hidden @ X9 @ (sk_C @ X8)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (sk_C @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('condensation', [status(thm)], ['68'])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((![X0 : $i]: ~ (r2_hidden @ sk_D @ X0))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['67', '69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((![X0 : $i]: (r2_hidden @ sk_D @ X0))
% 0.20/0.51         <= (((r2_hidden @ sk_D @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51                = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k8_relset_1 @ sk_A @ sk_B @ sk_C_2 @ (k1_tarski @ sk_D))
% 0.20/0.51          = (k1_xboole_0))) | 
% 0.20/0.51       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_D @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.51  thf('73', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '3', '37', '39', '72'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
