%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mEjAS3ZFSJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  24 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   89 ( 281 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   15 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t3_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                 => ( ( ( ( u1_struct_0 @ A )
                        = ( u1_struct_0 @ B ) )
                      & ( C = D )
                      & ( m1_setfam_1 @ C @ ( u1_struct_0 @ A ) ) )
                   => ( m1_setfam_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                   => ( ( ( ( u1_struct_0 @ A )
                          = ( u1_struct_0 @ B ) )
                        & ( C = D )
                        & ( m1_setfam_1 @ C @ ( u1_struct_0 @ A ) ) )
                     => ( m1_setfam_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_waybel_9])).

thf('0',plain,(
    ~ ( m1_setfam_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( m1_setfam_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( m1_setfam_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_setfam_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['4','5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mEjAS3ZFSJ
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:11:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 6 iterations in 0.007s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.46  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(t3_waybel_9, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_struct_0 @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( l1_struct_0 @ B ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m1_subset_1 @
% 0.21/0.46                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.46               ( ![D:$i]:
% 0.21/0.46                 ( ( m1_subset_1 @
% 0.21/0.46                     D @ 
% 0.21/0.46                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.46                   ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.21/0.46                       ( ( C ) = ( D ) ) & 
% 0.21/0.46                       ( m1_setfam_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46                     ( m1_setfam_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( l1_struct_0 @ A ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( l1_struct_0 @ B ) =>
% 0.21/0.46              ( ![C:$i]:
% 0.21/0.46                ( ( m1_subset_1 @
% 0.21/0.46                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.46                  ( ![D:$i]:
% 0.21/0.46                    ( ( m1_subset_1 @
% 0.21/0.46                        D @ 
% 0.21/0.46                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.46                      ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.21/0.46                          ( ( C ) = ( D ) ) & 
% 0.21/0.46                          ( m1_setfam_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.46                        ( m1_setfam_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t3_waybel_9])).
% 0.21/0.46  thf('0', plain, (~ (m1_setfam_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, (((sk_C) = (sk_D))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('2', plain, (~ (m1_setfam_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain, (~ (m1_setfam_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf('5', plain, ((m1_setfam_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain, ($false), inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
