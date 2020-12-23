%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:31 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   49 (  84 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 ( 136 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_11] :
      ( A_11 = '#skF_3'
      | ~ v1_xboole_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2])).

tff(c_49,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_24,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    m1_setfam_1('#skF_1',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_24])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12])).

tff(c_51,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_32])).

tff(c_14,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_31,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_14])).

tff(c_52,plain,(
    k3_tarski('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_49,c_31])).

tff(c_108,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k3_tarski(B_20))
      | ~ m1_setfam_1(B_20,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,'#skF_1')
      | ~ m1_setfam_1('#skF_1',A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_108])).

tff(c_122,plain,(
    ! [B_23,A_24] :
      ( B_23 = A_24
      | ~ r1_tarski(B_23,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_19] :
      ( A_19 = '#skF_1'
      | ~ r1_tarski('#skF_1',A_19)
      | ~ m1_setfam_1('#skF_1',A_19) ) ),
    inference(resolution,[status(thm)],[c_114,c_122])).

tff(c_157,plain,(
    ! [A_26] :
      ( A_26 = '#skF_1'
      | ~ m1_setfam_1('#skF_1',A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_124])).

tff(c_173,plain,(
    u1_struct_0('#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_58,c_157])).

tff(c_20,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_206,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_20])).

tff(c_210,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4,c_206])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.20  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.91/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.20  
% 1.91/1.21  tff(f_66, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.91/1.21  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.91/1.21  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.91/1.21  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.91/1.21  tff(f_40, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.91/1.21  tff(f_44, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.91/1.21  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.91/1.21  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.91/1.21  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.91/1.21  tff(c_28, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.91/1.21  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.21  tff(c_22, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.91/1.21  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.21  tff(c_45, plain, (![A_11]: (A_11='#skF_3' | ~v1_xboole_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2])).
% 1.91/1.21  tff(c_49, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_4, c_45])).
% 1.91/1.21  tff(c_24, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.91/1.21  tff(c_58, plain, (m1_setfam_1('#skF_1', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_24])).
% 1.91/1.21  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.21  tff(c_32, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12])).
% 1.91/1.21  tff(c_51, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_32])).
% 1.91/1.21  tff(c_14, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.21  tff(c_31, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_14])).
% 1.91/1.21  tff(c_52, plain, (k3_tarski('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_49, c_31])).
% 1.91/1.21  tff(c_108, plain, (![A_19, B_20]: (r1_tarski(A_19, k3_tarski(B_20)) | ~m1_setfam_1(B_20, A_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.21  tff(c_114, plain, (![A_19]: (r1_tarski(A_19, '#skF_1') | ~m1_setfam_1('#skF_1', A_19))), inference(superposition, [status(thm), theory('equality')], [c_52, c_108])).
% 1.91/1.21  tff(c_122, plain, (![B_23, A_24]: (B_23=A_24 | ~r1_tarski(B_23, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.21  tff(c_124, plain, (![A_19]: (A_19='#skF_1' | ~r1_tarski('#skF_1', A_19) | ~m1_setfam_1('#skF_1', A_19))), inference(resolution, [status(thm)], [c_114, c_122])).
% 1.91/1.21  tff(c_157, plain, (![A_26]: (A_26='#skF_1' | ~m1_setfam_1('#skF_1', A_26))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_124])).
% 1.91/1.21  tff(c_173, plain, (u1_struct_0('#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_58, c_157])).
% 1.91/1.21  tff(c_20, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.21  tff(c_206, plain, (~v1_xboole_0('#skF_1') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_20])).
% 1.91/1.21  tff(c_210, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4, c_206])).
% 1.91/1.21  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_210])).
% 1.91/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  Inference rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Ref     : 0
% 1.91/1.21  #Sup     : 38
% 1.91/1.21  #Fact    : 0
% 1.91/1.21  #Define  : 0
% 1.91/1.21  #Split   : 0
% 1.91/1.21  #Chain   : 0
% 1.91/1.21  #Close   : 0
% 1.91/1.21  
% 1.91/1.21  Ordering : KBO
% 1.91/1.21  
% 1.91/1.21  Simplification rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Subsume      : 2
% 1.91/1.21  #Demod        : 27
% 1.91/1.21  #Tautology    : 25
% 1.91/1.21  #SimpNegUnit  : 1
% 1.91/1.21  #BackRed      : 6
% 1.91/1.21  
% 1.91/1.21  #Partial instantiations: 0
% 1.91/1.21  #Strategies tried      : 1
% 1.91/1.21  
% 1.91/1.21  Timing (in seconds)
% 1.91/1.21  ----------------------
% 1.91/1.21  Preprocessing        : 0.28
% 1.91/1.21  Parsing              : 0.16
% 1.91/1.21  CNF conversion       : 0.02
% 1.91/1.21  Main loop            : 0.14
% 1.91/1.21  Inferencing          : 0.05
% 1.91/1.21  Reduction            : 0.05
% 1.91/1.21  Demodulation         : 0.04
% 1.91/1.21  BG Simplification    : 0.01
% 1.91/1.21  Subsumption          : 0.02
% 1.91/1.21  Abstraction          : 0.01
% 1.91/1.21  MUC search           : 0.00
% 1.91/1.21  Cooper               : 0.00
% 1.91/1.21  Total                : 0.45
% 1.91/1.21  Index Insertion      : 0.00
% 1.91/1.21  Index Deletion       : 0.00
% 1.91/1.21  Index Matching       : 0.00
% 1.91/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
