%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 137 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 ( 663 expanded)
%              Number of equality atoms :   95 ( 417 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [E,F,G] :
              ( D = k3_mcart_1(E,F,G)
              & ~ ( k5_mcart_1(A,B,C,D) = E
                  & k6_mcart_1(A,B,C,D) = F
                  & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_1'(A_4,B_5,C_6,D_22),A_4)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_3'(A_4,B_5,C_6,D_22),C_6)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_2'(A_4,B_5,C_6,D_22),B_5)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k3_mcart_1('#skF_1'(A_116,B_117,C_118,D_119),'#skF_2'(A_116,B_117,C_118,D_119),'#skF_3'(A_116,B_117,C_118,D_119)) = D_119
      | ~ m1_subset_1(D_119,k3_zfmisc_1(A_116,B_117,C_118))
      | k1_xboole_0 = C_118
      | k1_xboole_0 = B_117
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [H_57,F_51,G_55] :
      ( H_57 = '#skF_7'
      | k3_mcart_1(F_51,G_55,H_57) != '#skF_8'
      | ~ m1_subset_1(H_57,'#skF_6')
      | ~ m1_subset_1(G_55,'#skF_5')
      | ~ m1_subset_1(F_51,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_128,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( '#skF_3'(A_120,B_121,C_122,D_123) = '#skF_7'
      | D_123 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_120,B_121,C_122,D_123),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_120,B_121,C_122,D_123),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_120,B_121,C_122,D_123),'#skF_4')
      | ~ m1_subset_1(D_123,k3_zfmisc_1(A_120,B_121,C_122))
      | k1_xboole_0 = C_122
      | k1_xboole_0 = B_121
      | k1_xboole_0 = A_120 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_26])).

tff(c_132,plain,(
    ! [A_4,C_6,D_22] :
      ( '#skF_3'(A_4,'#skF_5',C_6,D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_4,'#skF_5',C_6,D_22),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_4,'#skF_5',C_6,D_22),'#skF_4')
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,'#skF_5',C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_145,plain,(
    ! [A_131,C_132,D_133] :
      ( '#skF_3'(A_131,'#skF_5',C_132,D_133) = '#skF_7'
      | D_133 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_131,'#skF_5',C_132,D_133),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_131,'#skF_5',C_132,D_133),'#skF_4')
      | ~ m1_subset_1(D_133,k3_zfmisc_1(A_131,'#skF_5',C_132))
      | k1_xboole_0 = C_132
      | k1_xboole_0 = A_131 ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_132])).

tff(c_149,plain,(
    ! [A_4,D_22] :
      ( '#skF_3'(A_4,'#skF_5','#skF_6',D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_4,'#skF_5','#skF_6',D_22),'#skF_4')
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_154,plain,(
    ! [A_134,D_135] :
      ( '#skF_3'(A_134,'#skF_5','#skF_6',D_135) = '#skF_7'
      | D_135 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_134,'#skF_5','#skF_6',D_135),'#skF_4')
      | ~ m1_subset_1(D_135,k3_zfmisc_1(A_134,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_134 ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_20,c_149])).

tff(c_158,plain,(
    ! [D_22] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1(D_22,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_163,plain,(
    ! [D_136] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_136) = '#skF_7'
      | D_136 != '#skF_8'
      | ~ m1_subset_1(D_136,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_24,c_158])).

tff(c_182,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_163])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( k3_mcart_1('#skF_1'(A_4,B_5,C_6,D_22),'#skF_2'(A_4,B_5,C_6,D_22),'#skF_3'(A_4,B_5,C_6,D_22)) = D_22
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_189,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_4])).

tff(c_200,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_189])).

tff(c_201,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_200])).

tff(c_12,plain,(
    ! [F_42,A_34,G_43,E_41,B_35,C_36] :
      ( k7_mcart_1(A_34,B_35,C_36,k3_mcart_1(E_41,F_42,G_43)) = G_43
      | k1_xboole_0 = C_36
      | k1_xboole_0 = B_35
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k3_mcart_1(E_41,F_42,G_43),k3_zfmisc_1(A_34,B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_245,plain,(
    ! [A_34,B_35,C_36] :
      ( k7_mcart_1(A_34,B_35,C_36,k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7')) = '#skF_7'
      | k1_xboole_0 = C_36
      | k1_xboole_0 = B_35
      | k1_xboole_0 = A_34
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_34,B_35,C_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_12])).

tff(c_263,plain,(
    ! [A_144,B_145,C_146] :
      ( k7_mcart_1(A_144,B_145,C_146,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_146
      | k1_xboole_0 = B_145
      | k1_xboole_0 = A_144
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_144,B_145,C_146)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_245])).

tff(c_266,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_263])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.35  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.43/1.35  
% 2.43/1.35  %Foreground sorts:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Background operators:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Foreground operators:
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.43/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.35  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.43/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.43/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.43/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.35  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.43/1.35  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.43/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.43/1.35  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.35  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.43/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.43/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.35  
% 2.68/1.37  tff(f_98, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 2.68/1.37  tff(f_52, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.68/1.37  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 2.68/1.37  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.37  tff(c_22, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.37  tff(c_20, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.37  tff(c_18, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.37  tff(c_28, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.37  tff(c_10, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_1'(A_4, B_5, C_6, D_22), A_4) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.37  tff(c_6, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_3'(A_4, B_5, C_6, D_22), C_6) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.37  tff(c_8, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_2'(A_4, B_5, C_6, D_22), B_5) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.37  tff(c_99, plain, (![A_116, B_117, C_118, D_119]: (k3_mcart_1('#skF_1'(A_116, B_117, C_118, D_119), '#skF_2'(A_116, B_117, C_118, D_119), '#skF_3'(A_116, B_117, C_118, D_119))=D_119 | ~m1_subset_1(D_119, k3_zfmisc_1(A_116, B_117, C_118)) | k1_xboole_0=C_118 | k1_xboole_0=B_117 | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.37  tff(c_26, plain, (![H_57, F_51, G_55]: (H_57='#skF_7' | k3_mcart_1(F_51, G_55, H_57)!='#skF_8' | ~m1_subset_1(H_57, '#skF_6') | ~m1_subset_1(G_55, '#skF_5') | ~m1_subset_1(F_51, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.37  tff(c_128, plain, (![A_120, B_121, C_122, D_123]: ('#skF_3'(A_120, B_121, C_122, D_123)='#skF_7' | D_123!='#skF_8' | ~m1_subset_1('#skF_3'(A_120, B_121, C_122, D_123), '#skF_6') | ~m1_subset_1('#skF_2'(A_120, B_121, C_122, D_123), '#skF_5') | ~m1_subset_1('#skF_1'(A_120, B_121, C_122, D_123), '#skF_4') | ~m1_subset_1(D_123, k3_zfmisc_1(A_120, B_121, C_122)) | k1_xboole_0=C_122 | k1_xboole_0=B_121 | k1_xboole_0=A_120)), inference(superposition, [status(thm), theory('equality')], [c_99, c_26])).
% 2.68/1.37  tff(c_132, plain, (![A_4, C_6, D_22]: ('#skF_3'(A_4, '#skF_5', C_6, D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1('#skF_3'(A_4, '#skF_5', C_6, D_22), '#skF_6') | ~m1_subset_1('#skF_1'(A_4, '#skF_5', C_6, D_22), '#skF_4') | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, '#skF_5', C_6)) | k1_xboole_0=C_6 | k1_xboole_0='#skF_5' | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_8, c_128])).
% 2.68/1.37  tff(c_145, plain, (![A_131, C_132, D_133]: ('#skF_3'(A_131, '#skF_5', C_132, D_133)='#skF_7' | D_133!='#skF_8' | ~m1_subset_1('#skF_3'(A_131, '#skF_5', C_132, D_133), '#skF_6') | ~m1_subset_1('#skF_1'(A_131, '#skF_5', C_132, D_133), '#skF_4') | ~m1_subset_1(D_133, k3_zfmisc_1(A_131, '#skF_5', C_132)) | k1_xboole_0=C_132 | k1_xboole_0=A_131)), inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_132])).
% 2.68/1.37  tff(c_149, plain, (![A_4, D_22]: ('#skF_3'(A_4, '#skF_5', '#skF_6', D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1('#skF_1'(A_4, '#skF_5', '#skF_6', D_22), '#skF_4') | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_6, c_145])).
% 2.68/1.37  tff(c_154, plain, (![A_134, D_135]: ('#skF_3'(A_134, '#skF_5', '#skF_6', D_135)='#skF_7' | D_135!='#skF_8' | ~m1_subset_1('#skF_1'(A_134, '#skF_5', '#skF_6', D_135), '#skF_4') | ~m1_subset_1(D_135, k3_zfmisc_1(A_134, '#skF_5', '#skF_6')) | k1_xboole_0=A_134)), inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_20, c_149])).
% 2.68/1.37  tff(c_158, plain, (![D_22]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1(D_22, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_10, c_154])).
% 2.68/1.37  tff(c_163, plain, (![D_136]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_136)='#skF_7' | D_136!='#skF_8' | ~m1_subset_1(D_136, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_24, c_158])).
% 2.68/1.37  tff(c_182, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_28, c_163])).
% 2.68/1.37  tff(c_4, plain, (![A_4, B_5, C_6, D_22]: (k3_mcart_1('#skF_1'(A_4, B_5, C_6, D_22), '#skF_2'(A_4, B_5, C_6, D_22), '#skF_3'(A_4, B_5, C_6, D_22))=D_22 | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.37  tff(c_189, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_182, c_4])).
% 2.68/1.37  tff(c_200, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_189])).
% 2.68/1.37  tff(c_201, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_200])).
% 2.68/1.37  tff(c_12, plain, (![F_42, A_34, G_43, E_41, B_35, C_36]: (k7_mcart_1(A_34, B_35, C_36, k3_mcart_1(E_41, F_42, G_43))=G_43 | k1_xboole_0=C_36 | k1_xboole_0=B_35 | k1_xboole_0=A_34 | ~m1_subset_1(k3_mcart_1(E_41, F_42, G_43), k3_zfmisc_1(A_34, B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.68/1.37  tff(c_245, plain, (![A_34, B_35, C_36]: (k7_mcart_1(A_34, B_35, C_36, k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7'))='#skF_7' | k1_xboole_0=C_36 | k1_xboole_0=B_35 | k1_xboole_0=A_34 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_34, B_35, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_201, c_12])).
% 2.68/1.37  tff(c_263, plain, (![A_144, B_145, C_146]: (k7_mcart_1(A_144, B_145, C_146, '#skF_8')='#skF_7' | k1_xboole_0=C_146 | k1_xboole_0=B_145 | k1_xboole_0=A_144 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_144, B_145, C_146)))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_245])).
% 2.68/1.37  tff(c_266, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_263])).
% 2.68/1.37  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_266])).
% 2.68/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  Inference rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Ref     : 0
% 2.68/1.37  #Sup     : 52
% 2.68/1.37  #Fact    : 0
% 2.68/1.37  #Define  : 0
% 2.68/1.37  #Split   : 0
% 2.68/1.37  #Chain   : 0
% 2.68/1.37  #Close   : 0
% 2.68/1.37  
% 2.68/1.37  Ordering : KBO
% 2.68/1.37  
% 2.68/1.37  Simplification rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Subsume      : 4
% 2.68/1.37  #Demod        : 30
% 2.68/1.37  #Tautology    : 16
% 2.68/1.37  #SimpNegUnit  : 8
% 2.68/1.37  #BackRed      : 0
% 2.68/1.37  
% 2.68/1.37  #Partial instantiations: 0
% 2.68/1.37  #Strategies tried      : 1
% 2.68/1.37  
% 2.68/1.37  Timing (in seconds)
% 2.68/1.37  ----------------------
% 2.68/1.37  Preprocessing        : 0.32
% 2.68/1.37  Parsing              : 0.17
% 2.68/1.37  CNF conversion       : 0.03
% 2.68/1.37  Main loop            : 0.27
% 2.68/1.37  Inferencing          : 0.11
% 2.68/1.38  Reduction            : 0.08
% 2.68/1.38  Demodulation         : 0.06
% 2.68/1.38  BG Simplification    : 0.02
% 2.68/1.38  Subsumption          : 0.05
% 2.68/1.38  Abstraction          : 0.02
% 2.68/1.38  MUC search           : 0.00
% 2.68/1.38  Cooper               : 0.00
% 2.68/1.38  Total                : 0.63
% 2.68/1.38  Index Insertion      : 0.00
% 2.68/1.38  Index Deletion       : 0.00
% 2.68/1.38  Index Matching       : 0.00
% 2.68/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
