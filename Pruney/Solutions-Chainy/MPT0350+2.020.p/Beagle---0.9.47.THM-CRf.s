%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:28 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 117 expanded)
%              Number of leaves         :   45 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 135 expanded)
%              Number of equality atoms :   46 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_93,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_54,plain,(
    ! [A_53] : k2_subset_1(A_53) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_64,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_67,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_269,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),A_93)
      | r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_289,plain,(
    ! [A_97] : r1_tarski(A_97,A_97) ),
    inference(resolution,[status(thm)],[c_269,c_4])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_294,plain,(
    ! [A_98] : k3_xboole_0(A_98,A_98) = A_98 ),
    inference(resolution,[status(thm)],[c_289,c_12])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_300,plain,(
    ! [A_98] : k2_xboole_0(A_98,A_98) = A_98 ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_10])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_293,plain,(
    ! [A_97] : k3_xboole_0(A_97,A_97) = A_97 ),
    inference(resolution,[status(thm)],[c_289,c_12])).

tff(c_316,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_325,plain,(
    ! [A_97] : k5_xboole_0(A_97,A_97) = k4_xboole_0(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_316])).

tff(c_333,plain,(
    ! [A_102] : k4_xboole_0(A_102,A_102) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_325])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_338,plain,(
    ! [A_102] : k2_xboole_0(A_102,k1_xboole_0) = k2_xboole_0(A_102,A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_14])).

tff(c_342,plain,(
    ! [A_102] : k2_xboole_0(A_102,k1_xboole_0) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_338])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    ! [A_58] : ~ v1_xboole_0(k1_zfmisc_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_191,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(B_85,A_86)
      | ~ m1_subset_1(B_85,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [C_48,A_44] :
      ( r1_tarski(C_48,A_44)
      | ~ r2_hidden(C_48,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_195,plain,(
    ! [B_85,A_44] :
      ( r1_tarski(B_85,A_44)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_44))
      | v1_xboole_0(k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_191,c_32])).

tff(c_244,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_195])).

tff(c_253,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_244])).

tff(c_257,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_253,c_12])).

tff(c_328,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_316])).

tff(c_332,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_328])).

tff(c_347,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_14])).

tff(c_492,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_347])).

tff(c_18,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_153,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_168,plain,(
    ! [B_83,A_84] : k3_tarski(k2_tarski(B_83,A_84)) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_153])).

tff(c_44,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_174,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_44])).

tff(c_579,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = k3_subset_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_592,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_579])).

tff(c_596,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_14])).

tff(c_599,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_174,c_596])).

tff(c_58,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k3_subset_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1149,plain,(
    ! [A_179,B_180,C_181] :
      ( k4_subset_1(A_179,B_180,C_181) = k2_xboole_0(B_180,C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(A_179))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4566,plain,(
    ! [A_297,B_298,B_299] :
      ( k4_subset_1(A_297,B_298,k3_subset_1(A_297,B_299)) = k2_xboole_0(B_298,k3_subset_1(A_297,B_299))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(A_297))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(A_297)) ) ),
    inference(resolution,[status(thm)],[c_58,c_1149])).

tff(c_4720,plain,(
    ! [B_302] :
      ( k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4',B_302)) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4',B_302))
      | ~ m1_subset_1(B_302,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_66,c_4566])).

tff(c_4762,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_4720])).

tff(c_4783,plain,(
    k4_subset_1('#skF_4','#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_4762])).

tff(c_4785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_4783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:42:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.03  
% 5.36/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.03  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 5.36/2.03  
% 5.36/2.03  %Foreground sorts:
% 5.36/2.03  
% 5.36/2.03  
% 5.36/2.03  %Background operators:
% 5.36/2.03  
% 5.36/2.03  
% 5.36/2.03  %Foreground operators:
% 5.36/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/2.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.36/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.36/2.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.36/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.36/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.36/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.36/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.36/2.03  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.36/2.03  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.36/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.36/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.36/2.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.36/2.03  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.36/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.36/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.36/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.36/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.36/2.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.36/2.03  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.36/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.36/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.36/2.03  
% 5.36/2.05  tff(f_82, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.36/2.05  tff(f_104, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 5.36/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.36/2.05  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.36/2.05  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.36/2.05  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.36/2.05  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.36/2.05  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.36/2.05  tff(f_93, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.36/2.05  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.36/2.05  tff(f_65, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.36/2.05  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.36/2.05  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.36/2.05  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.36/2.05  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.36/2.05  tff(f_99, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.36/2.05  tff(c_54, plain, (![A_53]: (k2_subset_1(A_53)=A_53)), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.36/2.05  tff(c_64, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.36/2.05  tff(c_67, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64])).
% 5.36/2.05  tff(c_269, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), A_93) | r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.05  tff(c_289, plain, (![A_97]: (r1_tarski(A_97, A_97))), inference(resolution, [status(thm)], [c_269, c_4])).
% 5.36/2.05  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.36/2.05  tff(c_294, plain, (![A_98]: (k3_xboole_0(A_98, A_98)=A_98)), inference(resolution, [status(thm)], [c_289, c_12])).
% 5.36/2.05  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.36/2.05  tff(c_300, plain, (![A_98]: (k2_xboole_0(A_98, A_98)=A_98)), inference(superposition, [status(thm), theory('equality')], [c_294, c_10])).
% 5.36/2.05  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.36/2.05  tff(c_293, plain, (![A_97]: (k3_xboole_0(A_97, A_97)=A_97)), inference(resolution, [status(thm)], [c_289, c_12])).
% 5.36/2.05  tff(c_316, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.36/2.05  tff(c_325, plain, (![A_97]: (k5_xboole_0(A_97, A_97)=k4_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_293, c_316])).
% 5.36/2.05  tff(c_333, plain, (![A_102]: (k4_xboole_0(A_102, A_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_325])).
% 5.36/2.05  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.36/2.05  tff(c_338, plain, (![A_102]: (k2_xboole_0(A_102, k1_xboole_0)=k2_xboole_0(A_102, A_102))), inference(superposition, [status(thm), theory('equality')], [c_333, c_14])).
% 5.36/2.05  tff(c_342, plain, (![A_102]: (k2_xboole_0(A_102, k1_xboole_0)=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_300, c_338])).
% 5.36/2.05  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.36/2.05  tff(c_60, plain, (![A_58]: (~v1_xboole_0(k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.36/2.05  tff(c_191, plain, (![B_85, A_86]: (r2_hidden(B_85, A_86) | ~m1_subset_1(B_85, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.36/2.05  tff(c_32, plain, (![C_48, A_44]: (r1_tarski(C_48, A_44) | ~r2_hidden(C_48, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.36/2.05  tff(c_195, plain, (![B_85, A_44]: (r1_tarski(B_85, A_44) | ~m1_subset_1(B_85, k1_zfmisc_1(A_44)) | v1_xboole_0(k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_191, c_32])).
% 5.36/2.05  tff(c_244, plain, (![B_91, A_92]: (r1_tarski(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)))), inference(negUnitSimplification, [status(thm)], [c_60, c_195])).
% 5.36/2.05  tff(c_253, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_244])).
% 5.36/2.05  tff(c_257, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_253, c_12])).
% 5.36/2.05  tff(c_328, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_257, c_316])).
% 5.36/2.05  tff(c_332, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_328])).
% 5.36/2.05  tff(c_347, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_332, c_14])).
% 5.36/2.05  tff(c_492, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_347])).
% 5.36/2.05  tff(c_18, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.36/2.05  tff(c_153, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.36/2.05  tff(c_168, plain, (![B_83, A_84]: (k3_tarski(k2_tarski(B_83, A_84))=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_18, c_153])).
% 5.36/2.05  tff(c_44, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.36/2.05  tff(c_174, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_168, c_44])).
% 5.36/2.05  tff(c_579, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=k3_subset_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.36/2.05  tff(c_592, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_579])).
% 5.36/2.05  tff(c_596, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_592, c_14])).
% 5.36/2.05  tff(c_599, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_174, c_596])).
% 5.36/2.05  tff(c_58, plain, (![A_56, B_57]: (m1_subset_1(k3_subset_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.36/2.05  tff(c_1149, plain, (![A_179, B_180, C_181]: (k4_subset_1(A_179, B_180, C_181)=k2_xboole_0(B_180, C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(A_179)) | ~m1_subset_1(B_180, k1_zfmisc_1(A_179)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.36/2.05  tff(c_4566, plain, (![A_297, B_298, B_299]: (k4_subset_1(A_297, B_298, k3_subset_1(A_297, B_299))=k2_xboole_0(B_298, k3_subset_1(A_297, B_299)) | ~m1_subset_1(B_298, k1_zfmisc_1(A_297)) | ~m1_subset_1(B_299, k1_zfmisc_1(A_297)))), inference(resolution, [status(thm)], [c_58, c_1149])).
% 5.36/2.05  tff(c_4720, plain, (![B_302]: (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', B_302))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', B_302)) | ~m1_subset_1(B_302, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_66, c_4566])).
% 5.36/2.05  tff(c_4762, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_4720])).
% 5.36/2.05  tff(c_4783, plain, (k4_subset_1('#skF_4', '#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_599, c_4762])).
% 5.36/2.05  tff(c_4785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_4783])).
% 5.36/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.05  
% 5.36/2.05  Inference rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Ref     : 0
% 5.36/2.05  #Sup     : 1042
% 5.36/2.05  #Fact    : 0
% 5.36/2.05  #Define  : 0
% 5.36/2.05  #Split   : 10
% 5.36/2.05  #Chain   : 0
% 5.36/2.05  #Close   : 0
% 5.36/2.05  
% 5.36/2.05  Ordering : KBO
% 5.36/2.05  
% 5.36/2.05  Simplification rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Subsume      : 107
% 5.36/2.05  #Demod        : 514
% 5.36/2.05  #Tautology    : 509
% 5.36/2.05  #SimpNegUnit  : 83
% 5.36/2.05  #BackRed      : 11
% 5.36/2.05  
% 5.36/2.05  #Partial instantiations: 0
% 5.36/2.05  #Strategies tried      : 1
% 5.36/2.05  
% 5.36/2.05  Timing (in seconds)
% 5.36/2.05  ----------------------
% 5.36/2.05  Preprocessing        : 0.34
% 5.36/2.05  Parsing              : 0.18
% 5.36/2.05  CNF conversion       : 0.02
% 5.36/2.05  Main loop            : 0.94
% 5.36/2.05  Inferencing          : 0.31
% 5.36/2.05  Reduction            : 0.33
% 5.36/2.05  Demodulation         : 0.24
% 5.36/2.05  BG Simplification    : 0.04
% 5.36/2.05  Subsumption          : 0.19
% 5.36/2.05  Abstraction          : 0.05
% 5.36/2.05  MUC search           : 0.00
% 5.36/2.05  Cooper               : 0.00
% 5.36/2.05  Total                : 1.32
% 5.36/2.05  Index Insertion      : 0.00
% 5.36/2.05  Index Deletion       : 0.00
% 5.36/2.05  Index Matching       : 0.00
% 5.36/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
