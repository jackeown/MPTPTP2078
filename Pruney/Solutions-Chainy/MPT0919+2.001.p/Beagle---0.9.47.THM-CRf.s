%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:15 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 189 expanded)
%              Number of equality atoms :   63 ( 105 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
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
                           => E = G ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k8_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

tff(c_20,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] :
      ( m1_subset_1(k10_mcart_1(A_15,B_16,C_17,D_18,E_19),C_17)
      | ~ m1_subset_1(E_19,k4_zfmisc_1(A_15,B_16,C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] :
      ( m1_subset_1(k11_mcart_1(A_20,B_21,C_22,D_23,E_24),D_23)
      | ~ m1_subset_1(E_24,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k8_mcart_1(A_25,B_26,C_27,D_28,E_29),A_25)
      | ~ m1_subset_1(E_29,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] :
      ( m1_subset_1(k9_mcart_1(A_30,B_31,C_32,D_33,E_34),B_31)
      | ~ m1_subset_1(E_34,k4_zfmisc_1(A_30,B_31,C_32,D_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_226,plain,(
    ! [E_140,A_137,B_141,C_138,D_139] :
      ( k4_mcart_1(k8_mcart_1(A_137,B_141,C_138,D_139,E_140),k9_mcart_1(A_137,B_141,C_138,D_139,E_140),k10_mcart_1(A_137,B_141,C_138,D_139,E_140),k11_mcart_1(A_137,B_141,C_138,D_139,E_140)) = E_140
      | ~ m1_subset_1(E_140,k4_zfmisc_1(A_137,B_141,C_138,D_139))
      | k1_xboole_0 = D_139
      | k1_xboole_0 = C_138
      | k1_xboole_0 = B_141
      | k1_xboole_0 = A_137 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [G_56,H_64,I_68,J_70] :
      ( G_56 = '#skF_5'
      | k4_mcart_1(G_56,H_64,I_68,J_70) != '#skF_6'
      | ~ m1_subset_1(J_70,'#skF_4')
      | ~ m1_subset_1(I_68,'#skF_3')
      | ~ m1_subset_1(H_64,'#skF_2')
      | ~ m1_subset_1(G_56,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_289,plain,(
    ! [C_159,B_163,D_160,A_162,E_161] :
      ( k8_mcart_1(A_162,B_163,C_159,D_160,E_161) = '#skF_5'
      | E_161 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1(A_162,B_163,C_159,D_160,E_161),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1(A_162,B_163,C_159,D_160,E_161),'#skF_3')
      | ~ m1_subset_1(k9_mcart_1(A_162,B_163,C_159,D_160,E_161),'#skF_2')
      | ~ m1_subset_1(k8_mcart_1(A_162,B_163,C_159,D_160,E_161),'#skF_1')
      | ~ m1_subset_1(E_161,k4_zfmisc_1(A_162,B_163,C_159,D_160))
      | k1_xboole_0 = D_160
      | k1_xboole_0 = C_159
      | k1_xboole_0 = B_163
      | k1_xboole_0 = A_162 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_30])).

tff(c_293,plain,(
    ! [A_30,C_32,D_33,E_34] :
      ( k8_mcart_1(A_30,'#skF_2',C_32,D_33,E_34) = '#skF_5'
      | E_34 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1(A_30,'#skF_2',C_32,D_33,E_34),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1(A_30,'#skF_2',C_32,D_33,E_34),'#skF_3')
      | ~ m1_subset_1(k8_mcart_1(A_30,'#skF_2',C_32,D_33,E_34),'#skF_1')
      | k1_xboole_0 = D_33
      | k1_xboole_0 = C_32
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(E_34,k4_zfmisc_1(A_30,'#skF_2',C_32,D_33)) ) ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_313,plain,(
    ! [A_170,C_171,D_172,E_173] :
      ( k8_mcart_1(A_170,'#skF_2',C_171,D_172,E_173) = '#skF_5'
      | E_173 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1(A_170,'#skF_2',C_171,D_172,E_173),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1(A_170,'#skF_2',C_171,D_172,E_173),'#skF_3')
      | ~ m1_subset_1(k8_mcart_1(A_170,'#skF_2',C_171,D_172,E_173),'#skF_1')
      | k1_xboole_0 = D_172
      | k1_xboole_0 = C_171
      | k1_xboole_0 = A_170
      | ~ m1_subset_1(E_173,k4_zfmisc_1(A_170,'#skF_2',C_171,D_172)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_293])).

tff(c_317,plain,(
    ! [C_27,D_28,E_29] :
      ( k8_mcart_1('#skF_1','#skF_2',C_27,D_28,E_29) = '#skF_5'
      | E_29 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1('#skF_1','#skF_2',C_27,D_28,E_29),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_27,D_28,E_29),'#skF_3')
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = '#skF_1'
      | ~ m1_subset_1(E_29,k4_zfmisc_1('#skF_1','#skF_2',C_27,D_28)) ) ),
    inference(resolution,[status(thm)],[c_14,c_313])).

tff(c_322,plain,(
    ! [C_174,D_175,E_176] :
      ( k8_mcart_1('#skF_1','#skF_2',C_174,D_175,E_176) = '#skF_5'
      | E_176 != '#skF_6'
      | ~ m1_subset_1(k11_mcart_1('#skF_1','#skF_2',C_174,D_175,E_176),'#skF_4')
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_174,D_175,E_176),'#skF_3')
      | k1_xboole_0 = D_175
      | k1_xboole_0 = C_174
      | ~ m1_subset_1(E_176,k4_zfmisc_1('#skF_1','#skF_2',C_174,D_175)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_317])).

tff(c_326,plain,(
    ! [C_22,E_24] :
      ( k8_mcart_1('#skF_1','#skF_2',C_22,'#skF_4',E_24) = '#skF_5'
      | E_24 != '#skF_6'
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_22,'#skF_4',E_24),'#skF_3')
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = C_22
      | ~ m1_subset_1(E_24,k4_zfmisc_1('#skF_1','#skF_2',C_22,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_322])).

tff(c_331,plain,(
    ! [C_177,E_178] :
      ( k8_mcart_1('#skF_1','#skF_2',C_177,'#skF_4',E_178) = '#skF_5'
      | E_178 != '#skF_6'
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2',C_177,'#skF_4',E_178),'#skF_3')
      | k1_xboole_0 = C_177
      | ~ m1_subset_1(E_178,k4_zfmisc_1('#skF_1','#skF_2',C_177,'#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_326])).

tff(c_335,plain,(
    ! [E_19] :
      ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4',E_19) = '#skF_5'
      | E_19 != '#skF_6'
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(E_19,k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_331])).

tff(c_340,plain,(
    ! [E_179] :
      ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4',E_179) = '#skF_5'
      | E_179 != '#skF_6'
      | ~ m1_subset_1(E_179,k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_335])).

tff(c_359,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_340])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.45/1.33  
% 2.45/1.33  %Foreground sorts:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Background operators:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Foreground operators:
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.45/1.33  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.45/1.33  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.45/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.33  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.45/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.33  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.45/1.33  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.33  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.33  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.45/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.33  
% 2.45/1.34  tff(f_97, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_mcart_1)).
% 2.45/1.34  tff(f_37, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k10_mcart_1(A, B, C, D, E), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 2.45/1.34  tff(f_41, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k11_mcart_1(A, B, C, D, E), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 2.45/1.34  tff(f_45, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k8_mcart_1(A, B, C, D, E), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 2.45/1.34  tff(f_49, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k9_mcart_1(A, B, C, D, E), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 2.45/1.34  tff(f_68, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_mcart_1)).
% 2.45/1.34  tff(c_20, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.45/1.34  tff(c_32, plain, (m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.45/1.34  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.45/1.34  tff(c_10, plain, (![B_16, A_15, D_18, E_19, C_17]: (m1_subset_1(k10_mcart_1(A_15, B_16, C_17, D_18, E_19), C_17) | ~m1_subset_1(E_19, k4_zfmisc_1(A_15, B_16, C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.34  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.45/1.34  tff(c_12, plain, (![C_22, D_23, A_20, B_21, E_24]: (m1_subset_1(k11_mcart_1(A_20, B_21, C_22, D_23, E_24), D_23) | ~m1_subset_1(E_24, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.34  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.45/1.34  tff(c_14, plain, (![A_25, E_29, C_27, D_28, B_26]: (m1_subset_1(k8_mcart_1(A_25, B_26, C_27, D_28, E_29), A_25) | ~m1_subset_1(E_29, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.34  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.45/1.34  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34]: (m1_subset_1(k9_mcart_1(A_30, B_31, C_32, D_33, E_34), B_31) | ~m1_subset_1(E_34, k4_zfmisc_1(A_30, B_31, C_32, D_33)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.45/1.34  tff(c_226, plain, (![E_140, A_137, B_141, C_138, D_139]: (k4_mcart_1(k8_mcart_1(A_137, B_141, C_138, D_139, E_140), k9_mcart_1(A_137, B_141, C_138, D_139, E_140), k10_mcart_1(A_137, B_141, C_138, D_139, E_140), k11_mcart_1(A_137, B_141, C_138, D_139, E_140))=E_140 | ~m1_subset_1(E_140, k4_zfmisc_1(A_137, B_141, C_138, D_139)) | k1_xboole_0=D_139 | k1_xboole_0=C_138 | k1_xboole_0=B_141 | k1_xboole_0=A_137)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.45/1.34  tff(c_30, plain, (![G_56, H_64, I_68, J_70]: (G_56='#skF_5' | k4_mcart_1(G_56, H_64, I_68, J_70)!='#skF_6' | ~m1_subset_1(J_70, '#skF_4') | ~m1_subset_1(I_68, '#skF_3') | ~m1_subset_1(H_64, '#skF_2') | ~m1_subset_1(G_56, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.45/1.34  tff(c_289, plain, (![C_159, B_163, D_160, A_162, E_161]: (k8_mcart_1(A_162, B_163, C_159, D_160, E_161)='#skF_5' | E_161!='#skF_6' | ~m1_subset_1(k11_mcart_1(A_162, B_163, C_159, D_160, E_161), '#skF_4') | ~m1_subset_1(k10_mcart_1(A_162, B_163, C_159, D_160, E_161), '#skF_3') | ~m1_subset_1(k9_mcart_1(A_162, B_163, C_159, D_160, E_161), '#skF_2') | ~m1_subset_1(k8_mcart_1(A_162, B_163, C_159, D_160, E_161), '#skF_1') | ~m1_subset_1(E_161, k4_zfmisc_1(A_162, B_163, C_159, D_160)) | k1_xboole_0=D_160 | k1_xboole_0=C_159 | k1_xboole_0=B_163 | k1_xboole_0=A_162)), inference(superposition, [status(thm), theory('equality')], [c_226, c_30])).
% 2.45/1.34  tff(c_293, plain, (![A_30, C_32, D_33, E_34]: (k8_mcart_1(A_30, '#skF_2', C_32, D_33, E_34)='#skF_5' | E_34!='#skF_6' | ~m1_subset_1(k11_mcart_1(A_30, '#skF_2', C_32, D_33, E_34), '#skF_4') | ~m1_subset_1(k10_mcart_1(A_30, '#skF_2', C_32, D_33, E_34), '#skF_3') | ~m1_subset_1(k8_mcart_1(A_30, '#skF_2', C_32, D_33, E_34), '#skF_1') | k1_xboole_0=D_33 | k1_xboole_0=C_32 | k1_xboole_0='#skF_2' | k1_xboole_0=A_30 | ~m1_subset_1(E_34, k4_zfmisc_1(A_30, '#skF_2', C_32, D_33)))), inference(resolution, [status(thm)], [c_16, c_289])).
% 2.45/1.34  tff(c_313, plain, (![A_170, C_171, D_172, E_173]: (k8_mcart_1(A_170, '#skF_2', C_171, D_172, E_173)='#skF_5' | E_173!='#skF_6' | ~m1_subset_1(k11_mcart_1(A_170, '#skF_2', C_171, D_172, E_173), '#skF_4') | ~m1_subset_1(k10_mcart_1(A_170, '#skF_2', C_171, D_172, E_173), '#skF_3') | ~m1_subset_1(k8_mcart_1(A_170, '#skF_2', C_171, D_172, E_173), '#skF_1') | k1_xboole_0=D_172 | k1_xboole_0=C_171 | k1_xboole_0=A_170 | ~m1_subset_1(E_173, k4_zfmisc_1(A_170, '#skF_2', C_171, D_172)))), inference(negUnitSimplification, [status(thm)], [c_26, c_293])).
% 2.45/1.34  tff(c_317, plain, (![C_27, D_28, E_29]: (k8_mcart_1('#skF_1', '#skF_2', C_27, D_28, E_29)='#skF_5' | E_29!='#skF_6' | ~m1_subset_1(k11_mcart_1('#skF_1', '#skF_2', C_27, D_28, E_29), '#skF_4') | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', C_27, D_28, E_29), '#skF_3') | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0='#skF_1' | ~m1_subset_1(E_29, k4_zfmisc_1('#skF_1', '#skF_2', C_27, D_28)))), inference(resolution, [status(thm)], [c_14, c_313])).
% 2.45/1.34  tff(c_322, plain, (![C_174, D_175, E_176]: (k8_mcart_1('#skF_1', '#skF_2', C_174, D_175, E_176)='#skF_5' | E_176!='#skF_6' | ~m1_subset_1(k11_mcart_1('#skF_1', '#skF_2', C_174, D_175, E_176), '#skF_4') | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', C_174, D_175, E_176), '#skF_3') | k1_xboole_0=D_175 | k1_xboole_0=C_174 | ~m1_subset_1(E_176, k4_zfmisc_1('#skF_1', '#skF_2', C_174, D_175)))), inference(negUnitSimplification, [status(thm)], [c_28, c_317])).
% 2.45/1.34  tff(c_326, plain, (![C_22, E_24]: (k8_mcart_1('#skF_1', '#skF_2', C_22, '#skF_4', E_24)='#skF_5' | E_24!='#skF_6' | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', C_22, '#skF_4', E_24), '#skF_3') | k1_xboole_0='#skF_4' | k1_xboole_0=C_22 | ~m1_subset_1(E_24, k4_zfmisc_1('#skF_1', '#skF_2', C_22, '#skF_4')))), inference(resolution, [status(thm)], [c_12, c_322])).
% 2.45/1.34  tff(c_331, plain, (![C_177, E_178]: (k8_mcart_1('#skF_1', '#skF_2', C_177, '#skF_4', E_178)='#skF_5' | E_178!='#skF_6' | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', C_177, '#skF_4', E_178), '#skF_3') | k1_xboole_0=C_177 | ~m1_subset_1(E_178, k4_zfmisc_1('#skF_1', '#skF_2', C_177, '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_22, c_326])).
% 2.45/1.34  tff(c_335, plain, (![E_19]: (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_19)='#skF_5' | E_19!='#skF_6' | k1_xboole_0='#skF_3' | ~m1_subset_1(E_19, k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_10, c_331])).
% 2.45/1.34  tff(c_340, plain, (![E_179]: (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_179)='#skF_5' | E_179!='#skF_6' | ~m1_subset_1(E_179, k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_24, c_335])).
% 2.45/1.34  tff(c_359, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_32, c_340])).
% 2.45/1.34  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_359])).
% 2.45/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  Inference rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Ref     : 0
% 2.45/1.34  #Sup     : 72
% 2.45/1.34  #Fact    : 0
% 2.45/1.34  #Define  : 0
% 2.45/1.34  #Split   : 0
% 2.45/1.34  #Chain   : 0
% 2.45/1.34  #Close   : 0
% 2.45/1.34  
% 2.45/1.34  Ordering : KBO
% 2.45/1.34  
% 2.45/1.34  Simplification rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Subsume      : 4
% 2.45/1.34  #Demod        : 62
% 2.45/1.34  #Tautology    : 46
% 2.45/1.34  #SimpNegUnit  : 5
% 2.45/1.34  #BackRed      : 0
% 2.45/1.34  
% 2.45/1.34  #Partial instantiations: 0
% 2.45/1.34  #Strategies tried      : 1
% 2.45/1.34  
% 2.45/1.34  Timing (in seconds)
% 2.45/1.34  ----------------------
% 2.45/1.34  Preprocessing        : 0.31
% 2.45/1.34  Parsing              : 0.17
% 2.45/1.34  CNF conversion       : 0.02
% 2.45/1.34  Main loop            : 0.25
% 2.45/1.34  Inferencing          : 0.11
% 2.45/1.34  Reduction            : 0.08
% 2.45/1.34  Demodulation         : 0.06
% 2.45/1.34  BG Simplification    : 0.02
% 2.45/1.34  Subsumption          : 0.04
% 2.45/1.34  Abstraction          : 0.02
% 2.45/1.34  MUC search           : 0.00
% 2.45/1.34  Cooper               : 0.00
% 2.45/1.34  Total                : 0.60
% 2.45/1.34  Index Insertion      : 0.00
% 2.45/1.34  Index Deletion       : 0.00
% 2.45/1.34  Index Matching       : 0.00
% 2.45/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
