%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:45 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  64 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k4_xboole_0(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_19,A_20] :
      ( r1_xboole_0(B_19,A_20)
      | ~ r1_xboole_0(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [B_7,A_6] : r1_xboole_0(B_7,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_24])).

tff(c_43,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_xboole_0(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_27,A_6,B_7] :
      ( r1_xboole_0(A_27,k4_xboole_0(A_6,B_7))
      | ~ r1_tarski(A_27,B_7) ) ),
    inference(resolution,[status(thm)],[c_27,c_43])).

tff(c_8,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k6_subset_1(B_16,k7_relat_1(B_16,A_15))) = k6_subset_1(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89,plain,(
    ! [B_47,A_48] :
      ( k1_relat_1(k4_xboole_0(B_47,k7_relat_1(B_47,A_48))) = k4_xboole_0(k1_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_14])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( k7_relat_1(A_12,B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,k1_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_150,plain,(
    ! [B_77,A_78,B_79] :
      ( k7_relat_1(k4_xboole_0(B_77,k7_relat_1(B_77,A_78)),B_79) = k1_xboole_0
      | ~ r1_xboole_0(B_79,k4_xboole_0(k1_relat_1(B_77),A_78))
      | ~ v1_relat_1(k4_xboole_0(B_77,k7_relat_1(B_77,A_78)))
      | ~ v1_relat_1(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_645,plain,(
    ! [B_154,B_155,A_156] :
      ( k7_relat_1(k4_xboole_0(B_154,k7_relat_1(B_154,B_155)),A_156) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_154,k7_relat_1(B_154,B_155)))
      | ~ v1_relat_1(B_154)
      | ~ r1_tarski(A_156,B_155) ) ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_706,plain,(
    ! [A_161,B_162,A_163] :
      ( k7_relat_1(k4_xboole_0(A_161,k7_relat_1(A_161,B_162)),A_163) = k1_xboole_0
      | ~ r1_tarski(A_163,B_162)
      | ~ v1_relat_1(A_161) ) ),
    inference(resolution,[status(thm)],[c_10,c_645])).

tff(c_16,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_754,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_22])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:48:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  
% 3.36/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.36/1.54  
% 3.36/1.54  %Foreground sorts:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Background operators:
% 3.36/1.54  
% 3.36/1.54  
% 3.36/1.54  %Foreground operators:
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.36/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.54  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.36/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.54  
% 3.36/1.55  tff(f_61, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 3.36/1.55  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 3.36/1.55  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.36/1.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.36/1.55  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.36/1.55  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.36/1.55  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 3.36/1.55  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 3.36/1.55  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.55  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.55  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k4_xboole_0(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.55  tff(c_6, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.55  tff(c_24, plain, (![B_19, A_20]: (r1_xboole_0(B_19, A_20) | ~r1_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.55  tff(c_27, plain, (![B_7, A_6]: (r1_xboole_0(B_7, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_6, c_24])).
% 3.36/1.55  tff(c_43, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_xboole_0(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.55  tff(c_48, plain, (![A_27, A_6, B_7]: (r1_xboole_0(A_27, k4_xboole_0(A_6, B_7)) | ~r1_tarski(A_27, B_7))), inference(resolution, [status(thm)], [c_27, c_43])).
% 3.36/1.55  tff(c_8, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.55  tff(c_14, plain, (![B_16, A_15]: (k1_relat_1(k6_subset_1(B_16, k7_relat_1(B_16, A_15)))=k6_subset_1(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.36/1.55  tff(c_89, plain, (![B_47, A_48]: (k1_relat_1(k4_xboole_0(B_47, k7_relat_1(B_47, A_48)))=k4_xboole_0(k1_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_14])).
% 3.36/1.55  tff(c_12, plain, (![A_12, B_14]: (k7_relat_1(A_12, B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, k1_relat_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.36/1.55  tff(c_150, plain, (![B_77, A_78, B_79]: (k7_relat_1(k4_xboole_0(B_77, k7_relat_1(B_77, A_78)), B_79)=k1_xboole_0 | ~r1_xboole_0(B_79, k4_xboole_0(k1_relat_1(B_77), A_78)) | ~v1_relat_1(k4_xboole_0(B_77, k7_relat_1(B_77, A_78))) | ~v1_relat_1(B_77))), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 3.36/1.55  tff(c_645, plain, (![B_154, B_155, A_156]: (k7_relat_1(k4_xboole_0(B_154, k7_relat_1(B_154, B_155)), A_156)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_154, k7_relat_1(B_154, B_155))) | ~v1_relat_1(B_154) | ~r1_tarski(A_156, B_155))), inference(resolution, [status(thm)], [c_48, c_150])).
% 3.36/1.55  tff(c_706, plain, (![A_161, B_162, A_163]: (k7_relat_1(k4_xboole_0(A_161, k7_relat_1(A_161, B_162)), A_163)=k1_xboole_0 | ~r1_tarski(A_163, B_162) | ~v1_relat_1(A_161))), inference(resolution, [status(thm)], [c_10, c_645])).
% 3.36/1.55  tff(c_16, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.55  tff(c_22, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 3.36/1.55  tff(c_754, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_706, c_22])).
% 3.36/1.55  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_754])).
% 3.36/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  Inference rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Ref     : 0
% 3.36/1.55  #Sup     : 233
% 3.36/1.55  #Fact    : 0
% 3.36/1.55  #Define  : 0
% 3.36/1.55  #Split   : 0
% 3.36/1.55  #Chain   : 0
% 3.36/1.55  #Close   : 0
% 3.36/1.55  
% 3.36/1.55  Ordering : KBO
% 3.36/1.55  
% 3.36/1.55  Simplification rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Subsume      : 19
% 3.36/1.55  #Demod        : 7
% 3.36/1.55  #Tautology    : 30
% 3.36/1.55  #SimpNegUnit  : 0
% 3.36/1.55  #BackRed      : 0
% 3.36/1.55  
% 3.36/1.55  #Partial instantiations: 0
% 3.36/1.55  #Strategies tried      : 1
% 3.36/1.55  
% 3.36/1.55  Timing (in seconds)
% 3.36/1.55  ----------------------
% 3.36/1.55  Preprocessing        : 0.30
% 3.36/1.55  Parsing              : 0.17
% 3.36/1.55  CNF conversion       : 0.02
% 3.36/1.55  Main loop            : 0.46
% 3.36/1.55  Inferencing          : 0.17
% 3.36/1.55  Reduction            : 0.11
% 3.36/1.55  Demodulation         : 0.08
% 3.36/1.55  BG Simplification    : 0.02
% 3.36/1.55  Subsumption          : 0.12
% 3.36/1.55  Abstraction          : 0.02
% 3.36/1.55  MUC search           : 0.00
% 3.36/1.56  Cooper               : 0.00
% 3.36/1.56  Total                : 0.79
% 3.36/1.56  Index Insertion      : 0.00
% 3.36/1.56  Index Deletion       : 0.00
% 3.36/1.56  Index Matching       : 0.00
% 3.36/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
