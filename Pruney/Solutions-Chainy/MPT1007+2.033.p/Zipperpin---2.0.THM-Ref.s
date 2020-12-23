%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TD9ZzQDQqQ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:20 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 322 expanded)
%              Number of leaves         :   43 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  960 (3484 expanded)
%              Number of equality atoms :   81 ( 193 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X17: $i] :
      ( ( ( k2_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('26',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24','25','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','33'])).

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

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( X20 = k1_xboole_0 )
      | ( X20
       != ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ X19 @ X18 )
        = k1_xboole_0 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X22 ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X22 ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('58',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['55','58'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k11_relat_1 @ X9 @ X10 )
        = ( k9_relat_1 @ X9 @ ( k1_tarski @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','65'])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('68',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ X19 @ X18 )
        = k1_xboole_0 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('71',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('72',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ( ( k11_relat_1 @ X13 @ X14 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('84',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('86',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['73','89'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','67','90'])).

thf('92',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('93',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['91','92'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('94',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TD9ZzQDQqQ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 143 iterations in 0.070s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.34/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.34/0.53  thf(t7_xboole_0, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.34/0.53  thf(t61_funct_2, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.34/0.53         ( m1_subset_1 @
% 0.34/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.34/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.34/0.53         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.34/0.53            ( m1_subset_1 @
% 0.34/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.34/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.34/0.53            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_C @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t7_funct_2, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.34/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.34/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X34 @ X35)
% 0.34/0.53          | ((X36) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_funct_1 @ X37)
% 0.34/0.53          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.34/0.53          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.34/0.53          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ X36))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.34/0.53          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.34/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.34/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.34/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.34/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.34/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.34/0.53  thf('7', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.34/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.34/0.53        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.34/0.53           sk_B_1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['0', '8'])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_C @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc2_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.34/0.53         ((v4_relat_1 @ X31 @ X32)
% 0.34/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.53  thf('12', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf(t209_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i]:
% 0.34/0.53         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.34/0.53          | ~ (v4_relat_1 @ X15 @ X16)
% 0.34/0.53          | ~ (v1_relat_1 @ X15))),
% 0.34/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.53        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_C @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc1_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.54       ( v1_relat_1 @ C ) ))).
% 0.34/0.54  thf('16', plain,
% 0.34/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.34/0.54         ((v1_relat_1 @ X28)
% 0.34/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.34/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.34/0.54  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('18', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.34/0.54      inference('demod', [status(thm)], ['14', '17'])).
% 0.34/0.54  thf(t148_relat_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ B ) =>
% 0.34/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.34/0.54  thf('19', plain,
% 0.34/0.54      (![X11 : $i, X12 : $i]:
% 0.34/0.54         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.34/0.54          | ~ (v1_relat_1 @ X11))),
% 0.34/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.34/0.54  thf(t64_relat_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ A ) =>
% 0.34/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.34/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.54  thf('20', plain,
% 0.34/0.54      (![X17 : $i]:
% 0.34/0.54         (((k2_relat_1 @ X17) != (k1_xboole_0))
% 0.34/0.54          | ((X17) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.34/0.54  thf('21', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X1)
% 0.34/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.34/0.54          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.54  thf('22', plain,
% 0.34/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.54        | ((k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.34/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.34/0.54        | ((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['18', '21'])).
% 0.34/0.54  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('24', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.34/0.54      inference('demod', [status(thm)], ['14', '17'])).
% 0.34/0.54  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('26', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.34/0.54      inference('demod', [status(thm)], ['14', '17'])).
% 0.34/0.54  thf('27', plain,
% 0.34/0.54      (![X11 : $i, X12 : $i]:
% 0.34/0.54         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.34/0.54          | ~ (v1_relat_1 @ X11))),
% 0.34/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.34/0.54  thf('28', plain,
% 0.34/0.54      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.34/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.34/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.34/0.54  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('30', plain,
% 0.34/0.54      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.34/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.34/0.54  thf('31', plain,
% 0.34/0.54      ((((sk_C) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.34/0.54      inference('demod', [status(thm)], ['22', '23', '24', '25', '30'])).
% 0.34/0.54  thf('32', plain,
% 0.34/0.54      ((m1_subset_1 @ sk_C @ 
% 0.34/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('33', plain,
% 0.34/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.34/0.54         ((v5_relat_1 @ X31 @ X33)
% 0.34/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.34/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.54  thf('34', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.34/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.54  thf(d4_funct_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.54       ( ![B:$i,C:$i]:
% 0.34/0.54         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.34/0.54             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.34/0.54               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.34/0.54           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.34/0.54             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.34/0.54               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.34/0.54  thf('35', plain,
% 0.34/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.34/0.54         ((r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.34/0.54          | ((X20) = (k1_xboole_0))
% 0.34/0.54          | ((X20) != (k1_funct_1 @ X19 @ X18))
% 0.34/0.54          | ~ (v1_funct_1 @ X19)
% 0.34/0.54          | ~ (v1_relat_1 @ X19))),
% 0.34/0.54      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.34/0.54  thf('36', plain,
% 0.34/0.54      (![X18 : $i, X19 : $i]:
% 0.34/0.54         (~ (v1_relat_1 @ X19)
% 0.34/0.54          | ~ (v1_funct_1 @ X19)
% 0.34/0.54          | ((k1_funct_1 @ X19 @ X18) = (k1_xboole_0))
% 0.34/0.54          | (r2_hidden @ X18 @ (k1_relat_1 @ X19)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.34/0.54  thf(t172_funct_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.54       ( ![C:$i]:
% 0.34/0.54         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.34/0.54           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.34/0.54  thf('37', plain,
% 0.34/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ X23 @ X22) @ X24)
% 0.34/0.54          | ~ (v1_funct_1 @ X23)
% 0.34/0.54          | ~ (v5_relat_1 @ X23 @ X24)
% 0.34/0.54          | ~ (v1_relat_1 @ X23))),
% 0.34/0.54      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.34/0.54  thf('38', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_funct_1 @ X0)
% 0.34/0.54          | ~ (v1_relat_1 @ X0)
% 0.34/0.54          | ~ (v1_relat_1 @ X0)
% 0.34/0.54          | ~ (v5_relat_1 @ X0 @ X2)
% 0.34/0.54          | ~ (v1_funct_1 @ X0)
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.34/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.34/0.54  thf('39', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.34/0.54          | ~ (v5_relat_1 @ X0 @ X2)
% 0.34/0.54          | ~ (v1_relat_1 @ X0)
% 0.34/0.54          | ~ (v1_funct_1 @ X0)
% 0.34/0.54          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.34/0.54  thf('40', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.34/0.54          | ~ (v1_relat_1 @ sk_C)
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['34', '39'])).
% 0.34/0.54  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('43', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.34/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.34/0.54  thf('44', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('45', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.54  thf('46', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.34/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.54  thf(t205_relat_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ B ) =>
% 0.34/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.34/0.54         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.34/0.54  thf('47', plain,
% 0.34/0.54      (![X13 : $i, X14 : $i]:
% 0.34/0.54         (((k11_relat_1 @ X13 @ X14) = (k1_xboole_0))
% 0.34/0.54          | (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.34/0.54          | ~ (v1_relat_1 @ X13))),
% 0.34/0.54      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.34/0.54  thf('48', plain,
% 0.34/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ X23 @ X22) @ X24)
% 0.34/0.54          | ~ (v1_funct_1 @ X23)
% 0.34/0.54          | ~ (v5_relat_1 @ X23 @ X24)
% 0.34/0.54          | ~ (v1_relat_1 @ X23))),
% 0.34/0.54      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.34/0.54  thf('49', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         (~ (v1_relat_1 @ X0)
% 0.34/0.54          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X0)
% 0.34/0.54          | ~ (v5_relat_1 @ X0 @ X2)
% 0.34/0.54          | ~ (v1_funct_1 @ X0)
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.34/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.34/0.54  thf('50', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.34/0.54          | ~ (v1_funct_1 @ X0)
% 0.34/0.54          | ~ (v5_relat_1 @ X0 @ X2)
% 0.34/0.54          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X0))),
% 0.34/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.34/0.54  thf('51', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (v1_relat_1 @ sk_C)
% 0.34/0.54          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['46', '50'])).
% 0.34/0.54  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('54', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.34/0.54          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.34/0.54      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.34/0.54  thf('55', plain,
% 0.34/0.54      (((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.34/0.54        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup+', [status(thm)], ['45', '54'])).
% 0.34/0.54  thf('56', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('57', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.54  thf('58', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.34/0.54      inference('demod', [status(thm)], ['56', '57'])).
% 0.34/0.54  thf('59', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.34/0.54      inference('clc', [status(thm)], ['55', '58'])).
% 0.34/0.54  thf(d16_relat_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ A ) =>
% 0.34/0.54       ( ![B:$i]:
% 0.34/0.54         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.34/0.54  thf('60', plain,
% 0.34/0.54      (![X9 : $i, X10 : $i]:
% 0.34/0.54         (((k11_relat_1 @ X9 @ X10) = (k9_relat_1 @ X9 @ (k1_tarski @ X10)))
% 0.34/0.54          | ~ (v1_relat_1 @ X9))),
% 0.34/0.54      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.34/0.54  thf('61', plain,
% 0.34/0.54      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.34/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.34/0.54  thf('62', plain,
% 0.34/0.54      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.34/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.34/0.54      inference('sup+', [status(thm)], ['60', '61'])).
% 0.34/0.54  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.54  thf('64', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.34/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.34/0.54  thf('65', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.34/0.54      inference('sup+', [status(thm)], ['59', '64'])).
% 0.34/0.54  thf('66', plain,
% 0.34/0.54      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.34/0.54      inference('demod', [status(thm)], ['31', '65'])).
% 0.34/0.54  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.34/0.54      inference('simplify', [status(thm)], ['66'])).
% 0.34/0.54  thf(t60_relat_1, axiom,
% 0.34/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.34/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.34/0.54  thf('68', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.34/0.54  thf('69', plain,
% 0.34/0.54      (![X18 : $i, X19 : $i]:
% 0.34/0.54         (~ (v1_relat_1 @ X19)
% 0.34/0.54          | ~ (v1_funct_1 @ X19)
% 0.34/0.54          | ((k1_funct_1 @ X19 @ X18) = (k1_xboole_0))
% 0.34/0.54          | (r2_hidden @ X18 @ (k1_relat_1 @ X19)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.34/0.54  thf('70', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.34/0.54          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.34/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.34/0.54      inference('sup+', [status(thm)], ['68', '69'])).
% 0.34/0.54  thf(t45_ordinal1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.34/0.54       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.34/0.54  thf('71', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.34/0.54      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.34/0.54  thf('72', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.54      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.34/0.54  thf('73', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.34/0.54          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.34/0.54  thf('74', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.34/0.54  thf('75', plain,
% 0.34/0.54      (![X13 : $i, X14 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.34/0.54          | ((k11_relat_1 @ X13 @ X14) != (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X13))),
% 0.34/0.54      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.34/0.54  thf('76', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.34/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.34/0.54          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['74', '75'])).
% 0.34/0.54  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.54      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.34/0.54  thf('78', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.34/0.54          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.34/0.54      inference('demod', [status(thm)], ['76', '77'])).
% 0.34/0.54  thf('79', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.34/0.54  thf('80', plain,
% 0.34/0.54      (![X13 : $i, X14 : $i]:
% 0.34/0.54         (((k11_relat_1 @ X13 @ X14) = (k1_xboole_0))
% 0.34/0.54          | (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.34/0.54          | ~ (v1_relat_1 @ X13))),
% 0.34/0.54      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.34/0.54  thf('81', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.34/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.34/0.54          | ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup+', [status(thm)], ['79', '80'])).
% 0.34/0.54  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.54      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.34/0.54  thf('83', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.34/0.54          | ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('demod', [status(thm)], ['81', '82'])).
% 0.34/0.54  thf(t7_ordinal1, axiom,
% 0.34/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.54  thf('84', plain,
% 0.34/0.54      (![X26 : $i, X27 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.34/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.34/0.54  thf('85', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['83', '84'])).
% 0.34/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.34/0.54  thf('86', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.34/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.34/0.54  thf('87', plain,
% 0.34/0.54      (![X0 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.54      inference('demod', [status(thm)], ['85', '86'])).
% 0.34/0.54  thf('88', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.34/0.54      inference('demod', [status(thm)], ['78', '87'])).
% 0.34/0.54  thf('89', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.54      inference('simplify', [status(thm)], ['88'])).
% 0.34/0.54  thf('90', plain,
% 0.34/0.54      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.34/0.54      inference('clc', [status(thm)], ['73', '89'])).
% 0.34/0.54  thf('91', plain,
% 0.34/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.34/0.54        | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.34/0.54      inference('demod', [status(thm)], ['9', '67', '90'])).
% 0.34/0.54  thf('92', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.34/0.54      inference('demod', [status(thm)], ['56', '57'])).
% 0.34/0.54  thf('93', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.34/0.54      inference('clc', [status(thm)], ['91', '92'])).
% 0.34/0.54  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.34/0.54  thf('94', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X8))),
% 0.34/0.54      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.34/0.54  thf('95', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.34/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.34/0.54  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.34/0.54  thf('97', plain, ($false), inference('demod', [status(thm)], ['95', '96'])).
% 0.34/0.54  
% 0.34/0.54  % SZS output end Refutation
% 0.34/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
