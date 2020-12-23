%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fsRzMLnxE6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:17 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 917 expanded)
%              Number of leaves         :   45 ( 286 expanded)
%              Depth                    :   19
%              Number of atoms          :  927 (10698 expanded)
%              Number of equality atoms :   72 ( 553 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('18',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('20',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17','18','19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( X24 = k1_xboole_0 )
      | ( X24
       != ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k1_funct_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X27 @ X26 ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X27 @ X26 ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('52',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','52'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','59'])).

thf('61',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['3','61'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('63',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X40 @ X37 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('65',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k1_funct_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('68',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('78',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('82',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','79','82','83'])).

thf('85',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('88',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','88'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('90',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sup-',[status(thm)],['89','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fsRzMLnxE6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 157 iterations in 0.072s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.37/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.53  thf(existence_m1_subset_1, axiom,
% 0.37/0.53    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.37/0.53  thf('0', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 0.37/0.53      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.37/0.53  thf(t2_subset, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.53  thf('1', plain,
% 0.37/0.53      (![X10 : $i, X11 : $i]:
% 0.37/0.53         ((r2_hidden @ X10 @ X11)
% 0.37/0.53          | (v1_xboole_0 @ X11)
% 0.37/0.53          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.53  thf(t61_funct_2, conjecture,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.53         ( m1_subset_1 @
% 0.37/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.53         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.53            ( m1_subset_1 @
% 0.37/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.53            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      ((m1_subset_1 @ sk_C @ 
% 0.37/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      ((m1_subset_1 @ sk_C @ 
% 0.37/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(cc2_relset_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.53  thf('5', plain,
% 0.37/0.53      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.53         ((v4_relat_1 @ X34 @ X35)
% 0.37/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.37/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.53  thf('6', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.37/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.53  thf(t209_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X19 : $i, X20 : $i]:
% 0.37/0.53         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.37/0.53          | ~ (v4_relat_1 @ X19 @ X20)
% 0.37/0.53          | ~ (v1_relat_1 @ X19))),
% 0.37/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.53        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.53  thf('9', plain,
% 0.37/0.53      ((m1_subset_1 @ sk_C @ 
% 0.37/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(cc1_relset_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.53       ( v1_relat_1 @ C ) ))).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.53         ((v1_relat_1 @ X31)
% 0.37/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.37/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.53  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('12', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.37/0.53  thf(t148_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ B ) =>
% 0.37/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.53  thf('13', plain,
% 0.37/0.53      (![X15 : $i, X16 : $i]:
% 0.37/0.53         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.37/0.53          | ~ (v1_relat_1 @ X15))),
% 0.37/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.53  thf(t64_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.53           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.53         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X21 : $i]:
% 0.37/0.53         (((k2_relat_1 @ X21) != (k1_xboole_0))
% 0.37/0.53          | ((X21) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X21))),
% 0.37/0.53      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.53  thf('15', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X1)
% 0.37/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.53          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.53  thf('16', plain,
% 0.37/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.53        | ((k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.37/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.53        | ((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.53  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('18', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.37/0.53  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('20', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.37/0.53  thf('21', plain,
% 0.37/0.53      (![X15 : $i, X16 : $i]:
% 0.37/0.53         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.37/0.53          | ~ (v1_relat_1 @ X15))),
% 0.37/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.53  thf('22', plain,
% 0.37/0.53      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.37/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.53  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('24', plain,
% 0.37/0.53      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.53  thf('25', plain,
% 0.37/0.53      ((((sk_C) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.37/0.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '24'])).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      ((m1_subset_1 @ sk_C @ 
% 0.37/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('27', plain,
% 0.37/0.53      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.53         ((v5_relat_1 @ X34 @ X36)
% 0.37/0.53          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.37/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.53  thf('28', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.37/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.53  thf(d4_funct_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.53       ( ![B:$i,C:$i]:
% 0.37/0.53         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.37/0.53             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.37/0.53               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.53           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.37/0.53             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.37/0.53               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.37/0.53  thf('29', plain,
% 0.37/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.53         ((r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.37/0.53          | ((X24) = (k1_xboole_0))
% 0.37/0.53          | ((X24) != (k1_funct_1 @ X23 @ X22))
% 0.37/0.53          | ~ (v1_funct_1 @ X23)
% 0.37/0.53          | ~ (v1_relat_1 @ X23))),
% 0.37/0.53      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.37/0.53  thf('30', plain,
% 0.37/0.53      (![X22 : $i, X23 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X23)
% 0.37/0.53          | ~ (v1_funct_1 @ X23)
% 0.37/0.53          | ((k1_funct_1 @ X23 @ X22) = (k1_xboole_0))
% 0.37/0.53          | (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.53  thf(t172_funct_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.53       ( ![C:$i]:
% 0.37/0.53         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.53           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ X27 @ X26) @ X28)
% 0.37/0.53          | ~ (v1_funct_1 @ X27)
% 0.37/0.53          | ~ (v5_relat_1 @ X27 @ X28)
% 0.37/0.53          | ~ (v1_relat_1 @ X27))),
% 0.37/0.53      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.37/0.53  thf('32', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_funct_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.53          | ~ (v1_funct_1 @ X0)
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.37/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.53  thf('33', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.37/0.53          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v1_funct_1 @ X0)
% 0.37/0.53          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.53  thf('34', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.37/0.53          | ~ (v1_relat_1 @ sk_C)
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.37/0.53      inference('sup-', [status(thm)], ['28', '33'])).
% 0.37/0.53  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('37', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.37/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.37/0.53  thf('38', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('39', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.53  thf('40', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.37/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.53  thf(t205_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ B ) =>
% 0.37/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.37/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.53  thf('41', plain,
% 0.37/0.53      (![X17 : $i, X18 : $i]:
% 0.37/0.53         (((k11_relat_1 @ X17 @ X18) = (k1_xboole_0))
% 0.37/0.53          | (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 0.37/0.53          | ~ (v1_relat_1 @ X17))),
% 0.37/0.53      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.37/0.53  thf('42', plain,
% 0.37/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ X27 @ X26) @ X28)
% 0.37/0.53          | ~ (v1_funct_1 @ X27)
% 0.37/0.53          | ~ (v5_relat_1 @ X27 @ X28)
% 0.37/0.53          | ~ (v1_relat_1 @ X27))),
% 0.37/0.53      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.37/0.53  thf('43', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.53          | ~ (v1_funct_1 @ X0)
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.37/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.53  thf('44', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.37/0.53          | ~ (v1_funct_1 @ X0)
% 0.37/0.53          | ~ (v5_relat_1 @ X0 @ X2)
% 0.37/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.53  thf('45', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ sk_C)
% 0.37/0.53          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.37/0.53      inference('sup-', [status(thm)], ['40', '44'])).
% 0.37/0.53  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('48', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.37/0.53      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.37/0.53  thf('49', plain,
% 0.37/0.53      (((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.37/0.53        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup+', [status(thm)], ['39', '48'])).
% 0.37/0.53  thf('50', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('51', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.53  thf('52', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.37/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.53  thf('53', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.37/0.53      inference('clc', [status(thm)], ['49', '52'])).
% 0.37/0.53  thf(d16_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ![B:$i]:
% 0.37/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.37/0.53  thf('54', plain,
% 0.37/0.53      (![X13 : $i, X14 : $i]:
% 0.37/0.53         (((k11_relat_1 @ X13 @ X14) = (k9_relat_1 @ X13 @ (k1_tarski @ X14)))
% 0.37/0.53          | ~ (v1_relat_1 @ X13))),
% 0.37/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.37/0.53  thf('55', plain,
% 0.37/0.53      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.53  thf('56', plain,
% 0.37/0.53      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.37/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.53      inference('sup+', [status(thm)], ['54', '55'])).
% 0.37/0.53  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('58', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.37/0.53      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.53  thf('59', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['53', '58'])).
% 0.37/0.53  thf('60', plain,
% 0.37/0.53      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.53      inference('demod', [status(thm)], ['25', '59'])).
% 0.37/0.53  thf('61', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.53  thf('62', plain,
% 0.37/0.53      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.37/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.37/0.53      inference('demod', [status(thm)], ['3', '61'])).
% 0.37/0.53  thf(t7_funct_2, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.37/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.37/0.53  thf('63', plain,
% 0.37/0.53      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X37 @ X38)
% 0.37/0.53          | ((X39) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_funct_1 @ X40)
% 0.37/0.53          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.37/0.53          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.37/0.53          | (r2_hidden @ (k1_funct_1 @ X40 @ X37) @ X39))),
% 0.37/0.53      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.37/0.53  thf('64', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ sk_B_1)
% 0.37/0.53          | ~ (v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.37/0.53          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.37/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.53  thf(cc1_relat_1, axiom,
% 0.37/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.37/0.53  thf('65', plain, (![X12 : $i]: ((v1_relat_1 @ X12) | ~ (v1_xboole_0 @ X12))),
% 0.37/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.53  thf(t60_relat_1, axiom,
% 0.37/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.53  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.53  thf('67', plain,
% 0.37/0.53      (![X22 : $i, X23 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X23)
% 0.37/0.53          | ~ (v1_funct_1 @ X23)
% 0.37/0.53          | ((k1_funct_1 @ X23 @ X22) = (k1_xboole_0))
% 0.37/0.53          | (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.53  thf(t7_ordinal1, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.53  thf('68', plain,
% 0.37/0.53      (![X29 : $i, X30 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.37/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.53  thf('69', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_funct_1 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.37/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.53  thf('70', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.37/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.53          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.37/0.53          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['66', '69'])).
% 0.37/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.53  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.53  thf('72', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.53          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.37/0.53          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.53  thf('73', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.53          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['65', '72'])).
% 0.37/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.53  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.53  thf('75', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.37/0.53          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.37/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.37/0.53  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('77', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.53  thf('78', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.37/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.37/0.53  thf('79', plain,
% 0.37/0.53      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.53      inference('demod', [status(thm)], ['75', '78'])).
% 0.37/0.53  thf('80', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('81', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.53  thf('82', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.37/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.37/0.53  thf('83', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.37/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.37/0.53  thf('84', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.37/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('demod', [status(thm)], ['64', '79', '82', '83'])).
% 0.37/0.53  thf('85', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('86', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.37/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.37/0.53      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.37/0.53  thf('87', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.37/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.53  thf('88', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.37/0.53      inference('clc', [status(thm)], ['86', '87'])).
% 0.37/0.53  thf('89', plain, ((v1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.37/0.53      inference('sup-', [status(thm)], ['2', '88'])).
% 0.37/0.53  thf(t69_enumset1, axiom,
% 0.37/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.53  thf('90', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.37/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.53  thf(fc3_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.37/0.53  thf('91', plain,
% 0.37/0.53      (![X7 : $i, X8 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X7 @ X8))),
% 0.37/0.53      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.37/0.53  thf('92', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['90', '91'])).
% 0.37/0.53  thf('93', plain, ($false), inference('sup-', [status(thm)], ['89', '92'])).
% 0.37/0.53  
% 0.37/0.53  % SZS output end Refutation
% 0.37/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
