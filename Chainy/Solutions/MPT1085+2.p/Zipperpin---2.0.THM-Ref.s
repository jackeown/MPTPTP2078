%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1085+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tMp3q93ixZ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 4.21s
% Output     : Refutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 154 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_100_type,type,(
    sk_B_100: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_17_type,type,(
    sk_A_17: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(t13_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( v1_finset_1 @ B ) )
       => ( v1_finset_1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t13_finset_1])).

thf('0',plain,(
    ~ ( v1_finset_1 @ sk_A_17 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( sk_A_17 @ sk_B_100 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( r1_tarski @ ( C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X961: $i,X962: $i,X963: $i] :
      ( ~ ( r1_tarski @ ( X961 @ X962 ) )
      | ( r2_hidden @ ( X961 @ X963 ) )
      | ( X963
       != ( k1_zfmisc_1 @ X962 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X961: $i,X962: $i] :
      ( ( r2_hidden @ ( X961 @ ( k1_zfmisc_1 @ X962 ) ) )
      | ~ ( r1_tarski @ ( X961 @ X962 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('5',plain,(
    ! [X961: $i,X962: $i] :
      ( ( r2_hidden @ ( X961 @ ( k9_setfam_1 @ X962 ) ) )
      | ~ ( r1_tarski @ ( X961 @ X962 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ ( sk_A_17 @ ( k9_setfam_1 @ sk_B_100 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( m1_subset_1 @ ( A @ B ) ) ) )).

thf('7',plain,(
    ! [X1932: $i,X1933: $i] :
      ( ( m1_subset_1 @ ( X1932 @ X1933 ) )
      | ~ ( r2_hidden @ ( X1932 @ X1933 ) ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('8',plain,(
    m1_subset_1 @ ( sk_A_17 @ ( k9_setfam_1 @ sk_B_100 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc2_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_finset_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X5683: $i,X5684: $i] :
      ( ~ ( m1_subset_1 @ ( X5683 @ ( k1_zfmisc_1 @ X5684 ) ) )
      | ( v1_finset_1 @ X5683 )
      | ~ ( v1_finset_1 @ X5684 ) ) ),
    inference(cnf,[status(esa)],[cc2_finset_1])).

thf('10',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('11',plain,(
    ! [X5683: $i,X5684: $i] :
      ( ~ ( m1_subset_1 @ ( X5683 @ ( k9_setfam_1 @ X5684 ) ) )
      | ( v1_finset_1 @ X5683 )
      | ~ ( v1_finset_1 @ X5684 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_finset_1 @ sk_B_100 )
    | ( v1_finset_1 @ sk_A_17 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_finset_1 @ sk_B_100 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_finset_1 @ sk_A_17 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
