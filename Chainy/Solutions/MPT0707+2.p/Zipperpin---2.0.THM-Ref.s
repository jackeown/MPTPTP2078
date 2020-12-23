%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0707+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bl739zFHnv

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 19.38s
% Output     : Refutation 19.38s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :  187 ( 220 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_27_type,type,(
    sk_B_27: $i )).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A @ B ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A @ B ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('0',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A_8 @ sk_B_27 ) )
 != sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B @ ( k6_relat_1 @ A ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2884: $i,X2885: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X2885 @ ( k6_relat_1 @ X2884 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( X2884 @ X2885 ) ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) )
            = ( k9_relat_1 @ ( B @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2337: $i,X2338: $i] :
      ( ~ ( v1_relat_1 @ X2337 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( X2338 @ X2337 ) ) )
        = ( k9_relat_1 @ ( X2337 @ ( k2_relat_1 @ X2338 ) ) ) )
      | ~ ( v1_relat_1 @ X2338 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('5',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    m1_subset_1 @ ( sk_B_27 @ ( k1_zfmisc_1 @ sk_A_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ ( sk_B_27 @ sk_A_8 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('13',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( sk_B_27 @ sk_A_8 ) )
    = sk_B_27 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_B_27 != sk_B_27 ),
    inference(demod,[status(thm)],['0','8','9','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
