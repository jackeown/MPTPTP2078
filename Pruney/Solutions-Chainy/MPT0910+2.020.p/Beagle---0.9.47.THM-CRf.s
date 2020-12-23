%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:02 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 131 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 514 expanded)
%              Number of equality atoms :   46 ( 314 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( m1_subset_1(k6_mcart_1(A_5,B_6,C_7,D_8),B_6)
      | ~ m1_subset_1(D_8,k3_zfmisc_1(A_5,B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k5_mcart_1(A_1,B_2,C_3,D_4),A_1)
      | ~ m1_subset_1(D_4,k3_zfmisc_1(A_1,B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_31,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k7_mcart_1(A_52,B_53,C_54,D_55) = k2_mcart_1(D_55)
      | ~ m1_subset_1(D_55,k3_zfmisc_1(A_52,B_53,C_54))
      | k1_xboole_0 = C_54
      | k1_xboole_0 = B_53
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_52,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_18,c_46])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k7_mcart_1(A_9,B_10,C_11,D_12),C_11)
      | ~ m1_subset_1(D_12,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_6])).

tff(c_60,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_56])).

tff(c_116,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k3_mcart_1(k5_mcart_1(A_64,B_65,C_66,D_67),k6_mcart_1(A_64,B_65,C_66,D_67),k7_mcart_1(A_64,B_65,C_66,D_67)) = D_67
      | ~ m1_subset_1(D_67,k3_zfmisc_1(A_64,B_65,C_66))
      | k1_xboole_0 = C_66
      | k1_xboole_0 = B_65
      | k1_xboole_0 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_127,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_116])).

tff(c_131,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_127])).

tff(c_132,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_18,c_131])).

tff(c_24,plain,(
    ! [G_34,F_30,H_36] :
      ( G_34 = '#skF_4'
      | k3_mcart_1(F_30,G_34,H_36) != '#skF_5'
      | ~ m1_subset_1(H_36,'#skF_3')
      | ~ m1_subset_1(G_34,'#skF_2')
      | ~ m1_subset_1(F_30,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_139,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_144,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_139])).

tff(c_145,plain,
    ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_144])).

tff(c_147,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_166,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_166])).

tff(c_171,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_175,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_171])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:44:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.28  
% 2.17/1.28  %Foreground sorts:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Background operators:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Foreground operators:
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.28  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.17/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.28  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.17/1.28  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.17/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.28  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.17/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.28  
% 2.17/1.29  tff(f_97, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 2.17/1.29  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 2.17/1.29  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 2.17/1.29  tff(f_73, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.17/1.29  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 2.17/1.29  tff(f_53, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.17/1.29  tff(c_26, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.29  tff(c_4, plain, (![A_5, B_6, C_7, D_8]: (m1_subset_1(k6_mcart_1(A_5, B_6, C_7, D_8), B_6) | ~m1_subset_1(D_8, k3_zfmisc_1(A_5, B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.29  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k5_mcart_1(A_1, B_2, C_3, D_4), A_1) | ~m1_subset_1(D_4, k3_zfmisc_1(A_1, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.29  tff(c_16, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.29  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.29  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.29  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.29  tff(c_31, plain, (![A_52, B_53, C_54, D_55]: (k7_mcart_1(A_52, B_53, C_54, D_55)=k2_mcart_1(D_55) | ~m1_subset_1(D_55, k3_zfmisc_1(A_52, B_53, C_54)) | k1_xboole_0=C_54 | k1_xboole_0=B_53 | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.29  tff(c_46, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_31])).
% 2.17/1.29  tff(c_52, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_18, c_46])).
% 2.17/1.29  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (m1_subset_1(k7_mcart_1(A_9, B_10, C_11, D_12), C_11) | ~m1_subset_1(D_12, k3_zfmisc_1(A_9, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.29  tff(c_56, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_6])).
% 2.17/1.29  tff(c_60, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_56])).
% 2.17/1.29  tff(c_116, plain, (![A_64, B_65, C_66, D_67]: (k3_mcart_1(k5_mcart_1(A_64, B_65, C_66, D_67), k6_mcart_1(A_64, B_65, C_66, D_67), k7_mcart_1(A_64, B_65, C_66, D_67))=D_67 | ~m1_subset_1(D_67, k3_zfmisc_1(A_64, B_65, C_66)) | k1_xboole_0=C_66 | k1_xboole_0=B_65 | k1_xboole_0=A_64)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.29  tff(c_127, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_52, c_116])).
% 2.17/1.29  tff(c_131, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_127])).
% 2.17/1.29  tff(c_132, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_18, c_131])).
% 2.17/1.29  tff(c_24, plain, (![G_34, F_30, H_36]: (G_34='#skF_4' | k3_mcart_1(F_30, G_34, H_36)!='#skF_5' | ~m1_subset_1(H_36, '#skF_3') | ~m1_subset_1(G_34, '#skF_2') | ~m1_subset_1(F_30, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.29  tff(c_139, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_132, c_24])).
% 2.17/1.29  tff(c_144, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_139])).
% 2.17/1.29  tff(c_145, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16, c_144])).
% 2.17/1.29  tff(c_147, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_145])).
% 2.17/1.29  tff(c_166, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_147])).
% 2.17/1.29  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_166])).
% 2.17/1.29  tff(c_171, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_145])).
% 2.17/1.29  tff(c_175, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_171])).
% 2.17/1.29  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_175])).
% 2.17/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  Inference rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Ref     : 0
% 2.17/1.29  #Sup     : 30
% 2.17/1.29  #Fact    : 0
% 2.17/1.29  #Define  : 0
% 2.17/1.29  #Split   : 1
% 2.17/1.29  #Chain   : 0
% 2.17/1.29  #Close   : 0
% 2.17/1.29  
% 2.17/1.29  Ordering : KBO
% 2.17/1.29  
% 2.17/1.29  Simplification rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Subsume      : 0
% 2.17/1.29  #Demod        : 7
% 2.17/1.29  #Tautology    : 10
% 2.17/1.29  #SimpNegUnit  : 7
% 2.17/1.29  #BackRed      : 0
% 2.17/1.29  
% 2.17/1.29  #Partial instantiations: 0
% 2.17/1.29  #Strategies tried      : 1
% 2.17/1.29  
% 2.17/1.29  Timing (in seconds)
% 2.17/1.29  ----------------------
% 2.17/1.29  Preprocessing        : 0.29
% 2.17/1.29  Parsing              : 0.15
% 2.17/1.29  CNF conversion       : 0.02
% 2.17/1.29  Main loop            : 0.19
% 2.17/1.29  Inferencing          : 0.08
% 2.17/1.29  Reduction            : 0.05
% 2.17/1.29  Demodulation         : 0.03
% 2.17/1.29  BG Simplification    : 0.02
% 2.17/1.29  Subsumption          : 0.03
% 2.17/1.29  Abstraction          : 0.02
% 2.17/1.29  MUC search           : 0.00
% 2.17/1.29  Cooper               : 0.00
% 2.17/1.29  Total                : 0.51
% 2.17/1.29  Index Insertion      : 0.00
% 2.17/1.29  Index Deletion       : 0.00
% 2.17/1.29  Index Matching       : 0.00
% 2.17/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
