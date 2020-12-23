%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 106 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 182 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,(
    ! [B_76,A_75] : r2_hidden(B_76,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_8])).

tff(c_48,plain,(
    ! [B_45,A_44] :
      ( r1_tarski(k1_setfam_1(B_45),A_44)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [B_85,A_86] :
      ( v1_relat_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,(
    ! [A_87,B_88] :
      ( v1_relat_1(A_87)
      | ~ v1_relat_1(B_88)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_129,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(k1_setfam_1(B_94))
      | ~ v1_relat_1(A_95)
      | ~ r2_hidden(A_95,B_94) ) ),
    inference(resolution,[status(thm)],[c_48,c_110])).

tff(c_133,plain,(
    ! [A_75,B_76] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_75,B_76)))
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_81,c_129])).

tff(c_143,plain,(
    ! [A_75,B_76] :
      ( v1_relat_1(k3_xboole_0(A_75,B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_133])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_101,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(k1_setfam_1(B_83),A_84)
      | ~ r2_hidden(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,(
    ! [A_111,B_112,A_113] :
      ( r1_tarski(k3_xboole_0(A_111,B_112),A_113)
      | ~ r2_hidden(A_113,k2_tarski(A_111,B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_101])).

tff(c_181,plain,(
    ! [A_75,B_76] : r1_tarski(k3_xboole_0(A_75,B_76),B_76) ),
    inference(resolution,[status(thm)],[c_81,c_172])).

tff(c_335,plain,(
    ! [C_164,A_165,B_166] :
      ( r1_tarski(k5_relat_1(C_164,A_165),k5_relat_1(C_164,B_166))
      | ~ r1_tarski(A_165,B_166)
      | ~ v1_relat_1(C_164)
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_252,plain,(
    ! [C_140,A_141,B_142] :
      ( r1_tarski(k5_relat_1(C_140,A_141),k5_relat_1(C_140,B_142))
      | ~ r1_tarski(A_141,B_142)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_187,plain,(
    ! [A_116,B_117,C_118] :
      ( r1_tarski(A_116,k3_xboole_0(B_117,C_118))
      | ~ r1_tarski(A_116,C_118)
      | ~ r1_tarski(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_195,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_187,c_54])).

tff(c_196,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_255,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_252,c_196])).

tff(c_261,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_2,c_255])).

tff(c_265,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_143,c_261])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_265])).

tff(c_273,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_338,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_335,c_273])).

tff(c_344,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_181,c_338])).

tff(c_348,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_143,c_344])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.38  
% 2.41/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.41/1.38  
% 2.41/1.38  %Foreground sorts:
% 2.41/1.38  
% 2.41/1.38  
% 2.41/1.38  %Background operators:
% 2.41/1.38  
% 2.41/1.38  
% 2.41/1.38  %Foreground operators:
% 2.41/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.41/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.41/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.41/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.38  
% 2.41/1.39  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.41/1.39  tff(f_62, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.41/1.39  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.41/1.39  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.41/1.39  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.41/1.39  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.41/1.39  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.41/1.39  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.41/1.39  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.41/1.39  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.41/1.39  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.41/1.39  tff(c_42, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.39  tff(c_75, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.39  tff(c_8, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.39  tff(c_81, plain, (![B_76, A_75]: (r2_hidden(B_76, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_8])).
% 2.41/1.39  tff(c_48, plain, (![B_45, A_44]: (r1_tarski(k1_setfam_1(B_45), A_44) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.39  tff(c_46, plain, (![A_42, B_43]: (m1_subset_1(A_42, k1_zfmisc_1(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.39  tff(c_105, plain, (![B_85, A_86]: (v1_relat_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.41/1.39  tff(c_110, plain, (![A_87, B_88]: (v1_relat_1(A_87) | ~v1_relat_1(B_88) | ~r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_46, c_105])).
% 2.41/1.39  tff(c_129, plain, (![B_94, A_95]: (v1_relat_1(k1_setfam_1(B_94)) | ~v1_relat_1(A_95) | ~r2_hidden(A_95, B_94))), inference(resolution, [status(thm)], [c_48, c_110])).
% 2.41/1.39  tff(c_133, plain, (![A_75, B_76]: (v1_relat_1(k1_setfam_1(k2_tarski(A_75, B_76))) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_81, c_129])).
% 2.41/1.39  tff(c_143, plain, (![A_75, B_76]: (v1_relat_1(k3_xboole_0(A_75, B_76)) | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_133])).
% 2.41/1.39  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.41/1.39  tff(c_101, plain, (![B_83, A_84]: (r1_tarski(k1_setfam_1(B_83), A_84) | ~r2_hidden(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.39  tff(c_172, plain, (![A_111, B_112, A_113]: (r1_tarski(k3_xboole_0(A_111, B_112), A_113) | ~r2_hidden(A_113, k2_tarski(A_111, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_101])).
% 2.41/1.39  tff(c_181, plain, (![A_75, B_76]: (r1_tarski(k3_xboole_0(A_75, B_76), B_76))), inference(resolution, [status(thm)], [c_81, c_172])).
% 2.41/1.39  tff(c_335, plain, (![C_164, A_165, B_166]: (r1_tarski(k5_relat_1(C_164, A_165), k5_relat_1(C_164, B_166)) | ~r1_tarski(A_165, B_166) | ~v1_relat_1(C_164) | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.41/1.39  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.41/1.39  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.39  tff(c_252, plain, (![C_140, A_141, B_142]: (r1_tarski(k5_relat_1(C_140, A_141), k5_relat_1(C_140, B_142)) | ~r1_tarski(A_141, B_142) | ~v1_relat_1(C_140) | ~v1_relat_1(B_142) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.41/1.39  tff(c_187, plain, (![A_116, B_117, C_118]: (r1_tarski(A_116, k3_xboole_0(B_117, C_118)) | ~r1_tarski(A_116, C_118) | ~r1_tarski(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.39  tff(c_54, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.41/1.39  tff(c_195, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_187, c_54])).
% 2.41/1.39  tff(c_196, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_195])).
% 2.41/1.39  tff(c_255, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_252, c_196])).
% 2.41/1.39  tff(c_261, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_2, c_255])).
% 2.41/1.39  tff(c_265, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_143, c_261])).
% 2.41/1.39  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_265])).
% 2.41/1.39  tff(c_273, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_195])).
% 2.41/1.39  tff(c_338, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_335, c_273])).
% 2.41/1.39  tff(c_344, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_181, c_338])).
% 2.41/1.39  tff(c_348, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_143, c_344])).
% 2.41/1.39  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_348])).
% 2.41/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.39  
% 2.41/1.39  Inference rules
% 2.41/1.39  ----------------------
% 2.41/1.39  #Ref     : 0
% 2.41/1.39  #Sup     : 62
% 2.41/1.39  #Fact    : 0
% 2.41/1.39  #Define  : 0
% 2.41/1.39  #Split   : 2
% 2.41/1.39  #Chain   : 0
% 2.41/1.39  #Close   : 0
% 2.41/1.39  
% 2.41/1.39  Ordering : KBO
% 2.41/1.39  
% 2.41/1.39  Simplification rules
% 2.41/1.39  ----------------------
% 2.41/1.39  #Subsume      : 9
% 2.41/1.39  #Demod        : 15
% 2.41/1.39  #Tautology    : 29
% 2.41/1.39  #SimpNegUnit  : 0
% 2.41/1.39  #BackRed      : 0
% 2.41/1.39  
% 2.41/1.39  #Partial instantiations: 0
% 2.41/1.39  #Strategies tried      : 1
% 2.41/1.39  
% 2.41/1.39  Timing (in seconds)
% 2.41/1.39  ----------------------
% 2.41/1.40  Preprocessing        : 0.35
% 2.41/1.40  Parsing              : 0.19
% 2.41/1.40  CNF conversion       : 0.03
% 2.41/1.40  Main loop            : 0.23
% 2.41/1.40  Inferencing          : 0.09
% 2.41/1.40  Reduction            : 0.06
% 2.41/1.40  Demodulation         : 0.05
% 2.41/1.40  BG Simplification    : 0.02
% 2.41/1.40  Subsumption          : 0.04
% 2.41/1.40  Abstraction          : 0.01
% 2.41/1.40  MUC search           : 0.00
% 2.41/1.40  Cooper               : 0.00
% 2.41/1.40  Total                : 0.61
% 2.41/1.40  Index Insertion      : 0.00
% 2.41/1.40  Index Deletion       : 0.00
% 2.41/1.40  Index Matching       : 0.00
% 2.41/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
