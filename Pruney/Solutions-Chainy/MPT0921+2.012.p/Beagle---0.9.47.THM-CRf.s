%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:19 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 210 expanded)
%              Number of leaves         :   26 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 (1036 expanded)
%              Number of equality atoms :   56 ( 627 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = I ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k10_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_8,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] :
      ( m1_subset_1(k9_mcart_1(A_16,B_17,C_18,D_19,E_20),B_17)
      | ~ m1_subset_1(E_20,k4_zfmisc_1(A_16,B_17,C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] :
      ( m1_subset_1(k10_mcart_1(A_1,B_2,C_3,D_4,E_5),C_3)
      | ~ m1_subset_1(E_5,k4_zfmisc_1(A_1,B_2,C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] :
      ( m1_subset_1(k8_mcart_1(A_11,B_12,C_13,D_14,E_15),A_11)
      | ~ m1_subset_1(E_15,k4_zfmisc_1(A_11,B_12,C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    ! [E_88,D_89,A_91,C_87,B_90] :
      ( k11_mcart_1(A_91,B_90,C_87,D_89,E_88) = k2_mcart_1(E_88)
      | ~ m1_subset_1(E_88,k4_zfmisc_1(A_91,B_90,C_87,D_89))
      | k1_xboole_0 = D_89
      | k1_xboole_0 = C_87
      | k1_xboole_0 = B_90
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_64,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_57])).

tff(c_4,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] :
      ( m1_subset_1(k11_mcart_1(A_6,B_7,C_8,D_9,E_10),D_9)
      | ~ m1_subset_1(E_10,k4_zfmisc_1(A_6,B_7,C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,
    ( m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4])).

tff(c_72,plain,(
    m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_165,plain,(
    ! [C_110,B_111,D_108,A_107,E_109] :
      ( k4_mcart_1(k8_mcart_1(A_107,B_111,C_110,D_108,E_109),k9_mcart_1(A_107,B_111,C_110,D_108,E_109),k10_mcart_1(A_107,B_111,C_110,D_108,E_109),k11_mcart_1(A_107,B_111,C_110,D_108,E_109)) = E_109
      | ~ m1_subset_1(E_109,k4_zfmisc_1(A_107,B_111,C_110,D_108))
      | k1_xboole_0 = D_108
      | k1_xboole_0 = C_110
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_176,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_165])).

tff(c_180,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_176])).

tff(c_181,plain,(
    k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_180])).

tff(c_30,plain,(
    ! [I_60,G_48,H_56,J_62] :
      ( I_60 = '#skF_5'
      | k4_mcart_1(G_48,H_56,I_60,J_62) != '#skF_6'
      | ~ m1_subset_1(J_62,'#skF_4')
      | ~ m1_subset_1(I_60,'#skF_3')
      | ~ m1_subset_1(H_56,'#skF_2')
      | ~ m1_subset_1(G_48,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_184,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4')
    | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
    | ~ m1_subset_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_30])).

tff(c_189,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
    | ~ m1_subset_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_184])).

tff(c_190,plain,
    ( ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
    | ~ m1_subset_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_189])).

tff(c_192,plain,(
    ~ m1_subset_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_195,plain,(
    ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_195])).

tff(c_200,plain,
    ( ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
    | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_219,plain,(
    ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_222,plain,(
    ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_222])).

tff(c_227,plain,(
    ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_231,plain,(
    ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_227])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n017.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 10:35:16 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.29  
% 2.27/1.29  %Foreground sorts:
% 2.27/1.29  
% 2.27/1.29  
% 2.27/1.29  %Background operators:
% 2.27/1.29  
% 2.27/1.29  
% 2.27/1.29  %Foreground operators:
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.29  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.29  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.27/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.29  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.29  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.27/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.27/1.29  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.29  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.27/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.29  
% 2.27/1.30  tff(f_114, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 2.27/1.30  tff(f_41, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k9_mcart_1(A, B, C, D, E), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 2.27/1.30  tff(f_29, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k10_mcart_1(A, B, C, D, E), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 2.27/1.30  tff(f_37, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k8_mcart_1(A, B, C, D, E), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 2.27/1.30  tff(f_85, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 2.27/1.30  tff(f_33, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k11_mcart_1(A, B, C, D, E), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 2.27/1.30  tff(f_60, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_mcart_1)).
% 2.27/1.30  tff(c_32, plain, (m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.27/1.30  tff(c_8, plain, (![C_18, B_17, A_16, D_19, E_20]: (m1_subset_1(k9_mcart_1(A_16, B_17, C_18, D_19, E_20), B_17) | ~m1_subset_1(E_20, k4_zfmisc_1(A_16, B_17, C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.30  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (m1_subset_1(k10_mcart_1(A_1, B_2, C_3, D_4, E_5), C_3) | ~m1_subset_1(E_5, k4_zfmisc_1(A_1, B_2, C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.30  tff(c_6, plain, (![D_14, E_15, B_12, A_11, C_13]: (m1_subset_1(k8_mcart_1(A_11, B_12, C_13, D_14, E_15), A_11) | ~m1_subset_1(E_15, k4_zfmisc_1(A_11, B_12, C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.30  tff(c_20, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.27/1.30  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.27/1.30  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.27/1.30  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.27/1.30  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.27/1.30  tff(c_38, plain, (![E_88, D_89, A_91, C_87, B_90]: (k11_mcart_1(A_91, B_90, C_87, D_89, E_88)=k2_mcart_1(E_88) | ~m1_subset_1(E_88, k4_zfmisc_1(A_91, B_90, C_87, D_89)) | k1_xboole_0=D_89 | k1_xboole_0=C_87 | k1_xboole_0=B_90 | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.30  tff(c_57, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.27/1.30  tff(c_64, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_57])).
% 2.27/1.30  tff(c_4, plain, (![B_7, D_9, C_8, E_10, A_6]: (m1_subset_1(k11_mcart_1(A_6, B_7, C_8, D_9, E_10), D_9) | ~m1_subset_1(E_10, k4_zfmisc_1(A_6, B_7, C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.30  tff(c_68, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4') | ~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4])).
% 2.27/1.30  tff(c_72, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 2.27/1.30  tff(c_165, plain, (![C_110, B_111, D_108, A_107, E_109]: (k4_mcart_1(k8_mcart_1(A_107, B_111, C_110, D_108, E_109), k9_mcart_1(A_107, B_111, C_110, D_108, E_109), k10_mcart_1(A_107, B_111, C_110, D_108, E_109), k11_mcart_1(A_107, B_111, C_110, D_108, E_109))=E_109 | ~m1_subset_1(E_109, k4_zfmisc_1(A_107, B_111, C_110, D_108)) | k1_xboole_0=D_108 | k1_xboole_0=C_110 | k1_xboole_0=B_111 | k1_xboole_0=A_107)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.30  tff(c_176, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_64, c_165])).
% 2.27/1.30  tff(c_180, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_176])).
% 2.27/1.30  tff(c_181, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_180])).
% 2.27/1.30  tff(c_30, plain, (![I_60, G_48, H_56, J_62]: (I_60='#skF_5' | k4_mcart_1(G_48, H_56, I_60, J_62)!='#skF_6' | ~m1_subset_1(J_62, '#skF_4') | ~m1_subset_1(I_60, '#skF_3') | ~m1_subset_1(H_56, '#skF_2') | ~m1_subset_1(G_48, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.27/1.30  tff(c_184, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4') | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | ~m1_subset_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_181, c_30])).
% 2.27/1.30  tff(c_189, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | ~m1_subset_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_184])).
% 2.27/1.30  tff(c_190, plain, (~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | ~m1_subset_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_20, c_189])).
% 2.27/1.30  tff(c_192, plain, (~m1_subset_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_1')), inference(splitLeft, [status(thm)], [c_190])).
% 2.27/1.30  tff(c_195, plain, (~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_192])).
% 2.27/1.30  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_195])).
% 2.27/1.30  tff(c_200, plain, (~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(splitRight, [status(thm)], [c_190])).
% 2.27/1.30  tff(c_219, plain, (~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_200])).
% 2.27/1.30  tff(c_222, plain, (~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_219])).
% 2.27/1.30  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_222])).
% 2.27/1.30  tff(c_227, plain, (~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(splitRight, [status(thm)], [c_200])).
% 2.27/1.30  tff(c_231, plain, (~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_227])).
% 2.27/1.30  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_231])).
% 2.27/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.30  
% 2.27/1.30  Inference rules
% 2.27/1.30  ----------------------
% 2.27/1.30  #Ref     : 0
% 2.27/1.30  #Sup     : 43
% 2.27/1.30  #Fact    : 0
% 2.27/1.30  #Define  : 0
% 2.27/1.30  #Split   : 2
% 2.27/1.30  #Chain   : 0
% 2.27/1.30  #Close   : 0
% 2.27/1.30  
% 2.27/1.30  Ordering : KBO
% 2.27/1.30  
% 2.27/1.30  Simplification rules
% 2.27/1.30  ----------------------
% 2.27/1.30  #Subsume      : 0
% 2.27/1.30  #Demod        : 6
% 2.27/1.30  #Tautology    : 12
% 2.27/1.30  #SimpNegUnit  : 6
% 2.27/1.30  #BackRed      : 0
% 2.27/1.30  
% 2.27/1.30  #Partial instantiations: 0
% 2.27/1.30  #Strategies tried      : 1
% 2.27/1.30  
% 2.27/1.30  Timing (in seconds)
% 2.27/1.30  ----------------------
% 2.27/1.30  Preprocessing        : 0.34
% 2.27/1.30  Parsing              : 0.18
% 2.27/1.30  CNF conversion       : 0.03
% 2.27/1.30  Main loop            : 0.22
% 2.27/1.30  Inferencing          : 0.09
% 2.27/1.30  Reduction            : 0.05
% 2.27/1.30  Demodulation         : 0.03
% 2.27/1.30  BG Simplification    : 0.02
% 2.27/1.31  Subsumption          : 0.04
% 2.27/1.31  Abstraction          : 0.02
% 2.27/1.31  MUC search           : 0.00
% 2.27/1.31  Cooper               : 0.00
% 2.27/1.31  Total                : 0.59
% 2.27/1.31  Index Insertion      : 0.00
% 2.27/1.31  Index Deletion       : 0.00
% 2.27/1.31  Index Matching       : 0.00
% 2.27/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
