%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0721+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6nLbTZrdh9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 16.13s
% Output     : Refutation 16.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  200 ( 360 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_12_type,type,(
    sk_A_12: $i )).

thf(sk_B_29_type,type,(
    sk_B_29: $i )).

thf(sk_C_52_type,type,(
    sk_C_52: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t176_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ ( C @ A ) )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( B @ ( k1_relat_1 @ C ) ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ ( C @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v5_relat_1 @ ( C @ A ) )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ ( B @ ( k1_relat_1 @ C ) ) )
         => ( m1_subset_1 @ ( k1_funct_1 @ ( C @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_funct_1 @ ( sk_C_52 @ sk_B_29 ) @ sk_A_12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_B_29 @ ( k1_relat_1 @ sk_C_52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ ( A @ D ) ) )
                  & ( r2_hidden @ ( D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2659: $i,X2661: $i,X2663: $i,X2664: $i] :
      ( ( X2661
       != ( k2_relat_1 @ X2659 ) )
      | ( r2_hidden @ ( X2663 @ X2661 ) )
      | ~ ( r2_hidden @ ( X2664 @ ( k1_relat_1 @ X2659 ) ) )
      | ( X2663
       != ( k1_funct_1 @ ( X2659 @ X2664 ) ) )
      | ~ ( v1_funct_1 @ X2659 )
      | ~ ( v1_relat_1 @ X2659 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X2659: $i,X2664: $i] :
      ( ~ ( v1_relat_1 @ X2659 )
      | ~ ( v1_funct_1 @ X2659 )
      | ~ ( r2_hidden @ ( X2664 @ ( k1_relat_1 @ X2659 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( X2659 @ X2664 ) @ ( k2_relat_1 @ X2659 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( sk_C_52 @ sk_B_29 ) @ ( k2_relat_1 @ sk_C_52 ) ) )
    | ~ ( v1_funct_1 @ sk_C_52 )
    | ~ ( v1_relat_1 @ sk_C_52 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C_52 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C_52 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( k1_funct_1 @ ( sk_C_52 @ sk_B_29 ) @ ( k2_relat_1 @ sk_C_52 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    v5_relat_1 @ ( sk_C_52 @ sk_A_12 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C_52 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_52 @ sk_A_12 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_52 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_52 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('13',plain,(
    ! [X1964: $i,X1966: $i] :
      ( ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1966 ) ) )
      | ~ ( r1_tarski @ ( X1964 @ X1966 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_52 @ ( k1_zfmisc_1 @ sk_A_12 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( A @ B ) )
        & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ C ) ) ) )
     => ( m1_subset_1 @ ( A @ C ) ) ) )).

thf('15',plain,(
    ! [X1985: $i,X1986: $i,X1987: $i] :
      ( ~ ( r2_hidden @ ( X1985 @ X1986 ) )
      | ~ ( m1_subset_1 @ ( X1986 @ ( k1_zfmisc_1 @ X1987 ) ) )
      | ( m1_subset_1 @ ( X1985 @ X1987 ) ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( X0 @ sk_A_12 ) )
      | ~ ( r2_hidden @ ( X0 @ ( k2_relat_1 @ sk_C_52 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_funct_1 @ ( sk_C_52 @ sk_B_29 ) @ sk_A_12 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
