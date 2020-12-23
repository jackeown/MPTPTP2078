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
% DateTime   : Thu Dec  3 09:45:22 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :   68 (  95 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 139 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_3568,plain,(
    ! [A_131,B_132] :
      ( r1_xboole_0(A_131,B_132)
      | k4_xboole_0(A_131,B_132) != A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3757,plain,(
    ! [B_139,A_140] :
      ( r1_xboole_0(B_139,A_140)
      | k4_xboole_0(A_140,B_139) != A_140 ) ),
    inference(resolution,[status(thm)],[c_3568,c_2])).

tff(c_80,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_84,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_58])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_185,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_200,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_185])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_720,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,k4_xboole_0(B_66,C_67))
      | ~ r1_xboole_0(A_65,C_67)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_736,plain,(
    ! [A_65,A_6,B_7] :
      ( ~ r1_xboole_0(A_65,k1_xboole_0)
      | ~ r1_xboole_0(A_65,A_6)
      | r1_xboole_0(A_65,k4_xboole_0(A_6,B_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_720])).

tff(c_2885,plain,(
    ! [A_108,A_109,B_110] :
      ( ~ r1_xboole_0(A_108,A_109)
      | r1_xboole_0(A_108,k4_xboole_0(A_109,B_110)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_736])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_199,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_742,plain,(
    ! [A_65] :
      ( ~ r1_xboole_0(A_65,k1_xboole_0)
      | ~ r1_xboole_0(A_65,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_65,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_720])).

tff(c_775,plain,(
    ! [A_65] :
      ( ~ r1_xboole_0(A_65,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_65,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_742])).

tff(c_2953,plain,(
    ! [A_111] :
      ( r1_xboole_0(A_111,'#skF_1')
      | ~ r1_xboole_0(A_111,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2885,c_775])).

tff(c_3095,plain,(
    ! [A_115] : r1_xboole_0(k4_xboole_0(A_115,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_2953])).

tff(c_3131,plain,(
    ! [A_116] : r1_xboole_0('#skF_1',k4_xboole_0(A_116,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_3095,c_2])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3272,plain,(
    ! [A_118] : k4_xboole_0('#skF_1',k4_xboole_0(A_118,'#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3131,c_22])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3325,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3272,c_16])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3426,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3325,c_14])).

tff(c_3449,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_3426])).

tff(c_3451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3449])).

tff(c_3452,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3768,plain,(
    k4_xboole_0('#skF_3','#skF_1') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3757,c_3452])).

tff(c_3454,plain,(
    ! [B_119,A_120] :
      ( r1_xboole_0(B_119,A_120)
      | ~ r1_xboole_0(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3459,plain,(
    ! [B_15,A_14] : r1_xboole_0(B_15,k4_xboole_0(A_14,B_15)) ),
    inference(resolution,[status(thm)],[c_20,c_3454])).

tff(c_3580,plain,(
    ! [A_133,B_134] :
      ( k4_xboole_0(A_133,B_134) = k1_xboole_0
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3598,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_3580])).

tff(c_4110,plain,(
    ! [A_153,B_154,C_155] :
      ( ~ r1_xboole_0(A_153,k4_xboole_0(B_154,C_155))
      | ~ r1_xboole_0(A_153,C_155)
      | r1_xboole_0(A_153,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4132,plain,(
    ! [A_153] :
      ( ~ r1_xboole_0(A_153,k1_xboole_0)
      | ~ r1_xboole_0(A_153,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_153,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3598,c_4110])).

tff(c_5335,plain,(
    ! [A_184] :
      ( ~ r1_xboole_0(A_184,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_184,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4132])).

tff(c_5375,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_3459,c_5335])).

tff(c_5379,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5375,c_22])).

tff(c_5385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3768,c_5379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:33:38 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.82  
% 4.21/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.82  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.21/1.82  
% 4.21/1.82  %Foreground sorts:
% 4.21/1.82  
% 4.21/1.82  
% 4.21/1.82  %Background operators:
% 4.21/1.82  
% 4.21/1.82  
% 4.21/1.82  %Foreground operators:
% 4.21/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.21/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.21/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.21/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.21/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.21/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.21/1.82  
% 4.21/1.84  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.21/1.84  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.21/1.84  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.21/1.84  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.21/1.84  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.21/1.84  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.21/1.84  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.21/1.84  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.21/1.84  tff(f_59, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 4.21/1.84  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.21/1.84  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.21/1.84  tff(c_3568, plain, (![A_131, B_132]: (r1_xboole_0(A_131, B_132) | k4_xboole_0(A_131, B_132)!=A_131)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.21/1.84  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.21/1.84  tff(c_3757, plain, (![B_139, A_140]: (r1_xboole_0(B_139, A_140) | k4_xboole_0(A_140, B_139)!=A_140)), inference(resolution, [status(thm)], [c_3568, c_2])).
% 4.21/1.84  tff(c_80, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.21/1.84  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.21/1.84  tff(c_58, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 4.21/1.84  tff(c_84, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_58])).
% 4.21/1.84  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.21/1.84  tff(c_48, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.21/1.84  tff(c_51, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_48])).
% 4.21/1.84  tff(c_185, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.21/1.84  tff(c_200, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_185])).
% 4.21/1.84  tff(c_20, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.21/1.84  tff(c_18, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.21/1.84  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.21/1.84  tff(c_201, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_185])).
% 4.21/1.84  tff(c_720, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, k4_xboole_0(B_66, C_67)) | ~r1_xboole_0(A_65, C_67) | r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.21/1.84  tff(c_736, plain, (![A_65, A_6, B_7]: (~r1_xboole_0(A_65, k1_xboole_0) | ~r1_xboole_0(A_65, A_6) | r1_xboole_0(A_65, k4_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_201, c_720])).
% 4.21/1.84  tff(c_2885, plain, (![A_108, A_109, B_110]: (~r1_xboole_0(A_108, A_109) | r1_xboole_0(A_108, k4_xboole_0(A_109, B_110)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_736])).
% 4.21/1.84  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.21/1.84  tff(c_199, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_185])).
% 4.21/1.84  tff(c_742, plain, (![A_65]: (~r1_xboole_0(A_65, k1_xboole_0) | ~r1_xboole_0(A_65, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_65, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_720])).
% 4.21/1.84  tff(c_775, plain, (![A_65]: (~r1_xboole_0(A_65, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_65, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_742])).
% 4.21/1.84  tff(c_2953, plain, (![A_111]: (r1_xboole_0(A_111, '#skF_1') | ~r1_xboole_0(A_111, '#skF_2'))), inference(resolution, [status(thm)], [c_2885, c_775])).
% 4.21/1.84  tff(c_3095, plain, (![A_115]: (r1_xboole_0(k4_xboole_0(A_115, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_2953])).
% 4.21/1.84  tff(c_3131, plain, (![A_116]: (r1_xboole_0('#skF_1', k4_xboole_0(A_116, '#skF_2')))), inference(resolution, [status(thm)], [c_3095, c_2])).
% 4.21/1.84  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.21/1.84  tff(c_3272, plain, (![A_118]: (k4_xboole_0('#skF_1', k4_xboole_0(A_118, '#skF_2'))='#skF_1')), inference(resolution, [status(thm)], [c_3131, c_22])).
% 4.21/1.84  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.21/1.84  tff(c_3325, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3272, c_16])).
% 4.21/1.84  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.21/1.84  tff(c_3426, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3325, c_14])).
% 4.21/1.84  tff(c_3449, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_200, c_3426])).
% 4.21/1.84  tff(c_3451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_3449])).
% 4.21/1.84  tff(c_3452, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 4.21/1.84  tff(c_3768, plain, (k4_xboole_0('#skF_3', '#skF_1')!='#skF_3'), inference(resolution, [status(thm)], [c_3757, c_3452])).
% 4.21/1.84  tff(c_3454, plain, (![B_119, A_120]: (r1_xboole_0(B_119, A_120) | ~r1_xboole_0(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.21/1.84  tff(c_3459, plain, (![B_15, A_14]: (r1_xboole_0(B_15, k4_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_20, c_3454])).
% 4.21/1.84  tff(c_3580, plain, (![A_133, B_134]: (k4_xboole_0(A_133, B_134)=k1_xboole_0 | ~r1_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.21/1.84  tff(c_3598, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_3580])).
% 4.21/1.84  tff(c_4110, plain, (![A_153, B_154, C_155]: (~r1_xboole_0(A_153, k4_xboole_0(B_154, C_155)) | ~r1_xboole_0(A_153, C_155) | r1_xboole_0(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.21/1.84  tff(c_4132, plain, (![A_153]: (~r1_xboole_0(A_153, k1_xboole_0) | ~r1_xboole_0(A_153, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_153, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3598, c_4110])).
% 4.21/1.84  tff(c_5335, plain, (![A_184]: (~r1_xboole_0(A_184, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_184, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4132])).
% 4.21/1.84  tff(c_5375, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_3459, c_5335])).
% 4.21/1.84  tff(c_5379, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_5375, c_22])).
% 4.21/1.84  tff(c_5385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3768, c_5379])).
% 4.21/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.84  
% 4.21/1.84  Inference rules
% 4.21/1.84  ----------------------
% 4.21/1.84  #Ref     : 0
% 4.21/1.84  #Sup     : 1355
% 4.21/1.84  #Fact    : 0
% 4.21/1.84  #Define  : 0
% 4.21/1.84  #Split   : 5
% 4.21/1.84  #Chain   : 0
% 4.21/1.84  #Close   : 0
% 4.21/1.84  
% 4.21/1.84  Ordering : KBO
% 4.21/1.84  
% 4.21/1.84  Simplification rules
% 4.21/1.84  ----------------------
% 4.21/1.84  #Subsume      : 283
% 4.21/1.84  #Demod        : 755
% 4.21/1.84  #Tautology    : 828
% 4.21/1.84  #SimpNegUnit  : 44
% 4.21/1.84  #BackRed      : 0
% 4.21/1.84  
% 4.21/1.84  #Partial instantiations: 0
% 4.21/1.84  #Strategies tried      : 1
% 4.21/1.84  
% 4.21/1.84  Timing (in seconds)
% 4.21/1.84  ----------------------
% 4.21/1.84  Preprocessing        : 0.30
% 4.21/1.84  Parsing              : 0.17
% 4.21/1.84  CNF conversion       : 0.02
% 4.21/1.84  Main loop            : 0.76
% 4.21/1.84  Inferencing          : 0.27
% 4.21/1.84  Reduction            : 0.30
% 4.21/1.84  Demodulation         : 0.22
% 4.21/1.84  BG Simplification    : 0.03
% 4.21/1.84  Subsumption          : 0.12
% 4.21/1.84  Abstraction          : 0.04
% 4.21/1.84  MUC search           : 0.00
% 4.21/1.84  Cooper               : 0.00
% 4.21/1.84  Total                : 1.09
% 4.21/1.84  Index Insertion      : 0.00
% 4.21/1.84  Index Deletion       : 0.00
% 4.21/1.84  Index Matching       : 0.00
% 4.21/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
