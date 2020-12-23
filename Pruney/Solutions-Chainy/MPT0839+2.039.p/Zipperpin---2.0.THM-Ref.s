%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hUxUxBJDFr

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 187 expanded)
%              Number of leaves         :   36 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  567 (1752 expanded)
%              Number of equality atoms :   32 (  71 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( ( k7_relat_1 @ X24 @ ( k1_relat_1 @ X24 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B )
    | ( r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['9','12'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X21 @ X19 ) @ X20 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k7_relat_1 @ sk_C_1 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('30',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','27','28','29'])).

thf('31',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','30'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X8: $i] :
      ( ( r1_xboole_0 @ X8 @ X8 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('37',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','46'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X16: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','51'])).

thf('53',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','27','28','29'])).

thf('55',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hUxUxBJDFr
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 114 iterations in 0.056s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(t50_relset_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.51               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51                    ( ![D:$i]:
% 0.20/0.51                      ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.51                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.51                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51                       ( ![D:$i]:
% 0.20/0.51                         ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.51                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t98_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X24 : $i]:
% 0.20/0.51         (((k7_relat_1 @ X24 @ (k1_relat_1 @ X24)) = (X24))
% 0.20/0.51          | ~ (v1_relat_1 @ X24))),
% 0.20/0.51      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.51  thf(t3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf(t1_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X0) | (m1_subset_1 @ (sk_C @ X0 @ X1) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X34 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X34 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X34 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ 
% 0.20/0.51               (sk_C @ X0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1)) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B)
% 0.20/0.51        | (r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B)),
% 0.20/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '12'])).
% 0.20/0.51  thf(t207_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.51         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ X19 @ X20)
% 0.20/0.51          | ~ (v1_relat_1 @ X21)
% 0.20/0.51          | ((k7_relat_1 @ (k7_relat_1 @ X21 @ X19) @ X20) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_C_1)) @ sk_B)
% 0.20/0.51            = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((((k7_relat_1 @ sk_C_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['1', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X25 @ X26)
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('19', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(t209_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X22 : $i, X23 : $i]:
% 0.20/0.51         (((X22) = (k7_relat_1 @ X22 @ X23))
% 0.20/0.51          | ~ (v4_relat_1 @ X22 @ X23)
% 0.20/0.51          | ~ (v1_relat_1 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.20/0.51          | (v1_relat_1 @ X14)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '26'])).
% 0.20/0.51  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('30', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '27', '28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '30'])).
% 0.20/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.51         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.20/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('35', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.20/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.51  thf(t66_xboole_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X8 : $i]: ((r1_xboole_0 @ X8 @ X8) | ((X8) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.51  thf('37', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X3 @ X4)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.51          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.51  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '43'])).
% 0.20/0.51  thf(t69_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ X10 @ X11)
% 0.20/0.51          | ~ (r1_tarski @ X10 @ X11)
% 0.20/0.51          | (v1_xboole_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '46'])).
% 0.20/0.51  thf(fc11_relat_1, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X16 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (k2_relat_1 @ X16)) | ~ (v1_xboole_0 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.20/0.51  thf(l13_xboole_0, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '51'])).
% 0.20/0.51  thf('53', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '27', '28', '29'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['52', '55'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
