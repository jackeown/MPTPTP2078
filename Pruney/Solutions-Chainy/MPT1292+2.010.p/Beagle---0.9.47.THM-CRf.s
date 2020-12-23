%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  80 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2])).

tff(c_22,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10])).

tff(c_12,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_12])).

tff(c_44,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k3_tarski(B_12))
      | ~ m1_setfam_1(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,'#skF_2')
      | ~ m1_setfam_1('#skF_2',A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_44])).

tff(c_73,plain,(
    ! [B_18,A_19] :
      ( B_18 = A_19
      | ~ r1_tarski(B_18,A_19)
      | ~ r1_tarski(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_11] :
      ( A_11 = '#skF_2'
      | ~ r1_tarski('#skF_2',A_11)
      | ~ m1_setfam_1('#skF_2',A_11) ) ),
    inference(resolution,[status(thm)],[c_47,c_73])).

tff(c_108,plain,(
    ! [A_21] :
      ( A_21 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_75])).

tff(c_124,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_108])).

tff(c_18,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_131,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_18])).

tff(c_135,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32,c_131])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.16  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.71/1.16  
% 1.71/1.16  %Foreground sorts:
% 1.71/1.16  
% 1.71/1.16  
% 1.71/1.16  %Background operators:
% 1.71/1.16  
% 1.71/1.16  
% 1.71/1.16  %Foreground operators:
% 1.71/1.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.71/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.16  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.71/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.71/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.71/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.71/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.71/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.16  
% 1.71/1.17  tff(f_61, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.71/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.71/1.17  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.71/1.17  tff(f_35, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.71/1.17  tff(f_39, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.71/1.17  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.71/1.17  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.71/1.17  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.71/1.17  tff(c_26, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.71/1.17  tff(c_20, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.71/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.71/1.17  tff(c_32, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2])).
% 1.71/1.17  tff(c_22, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.71/1.17  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.71/1.17  tff(c_30, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10])).
% 1.71/1.17  tff(c_12, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.17  tff(c_29, plain, (k3_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_12])).
% 1.71/1.17  tff(c_44, plain, (![A_11, B_12]: (r1_tarski(A_11, k3_tarski(B_12)) | ~m1_setfam_1(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.17  tff(c_47, plain, (![A_11]: (r1_tarski(A_11, '#skF_2') | ~m1_setfam_1('#skF_2', A_11))), inference(superposition, [status(thm), theory('equality')], [c_29, c_44])).
% 1.71/1.17  tff(c_73, plain, (![B_18, A_19]: (B_18=A_19 | ~r1_tarski(B_18, A_19) | ~r1_tarski(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.17  tff(c_75, plain, (![A_11]: (A_11='#skF_2' | ~r1_tarski('#skF_2', A_11) | ~m1_setfam_1('#skF_2', A_11))), inference(resolution, [status(thm)], [c_47, c_73])).
% 1.71/1.17  tff(c_108, plain, (![A_21]: (A_21='#skF_2' | ~m1_setfam_1('#skF_2', A_21))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_75])).
% 1.71/1.17  tff(c_124, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_108])).
% 1.71/1.17  tff(c_18, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.71/1.17  tff(c_131, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_124, c_18])).
% 1.71/1.17  tff(c_135, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32, c_131])).
% 1.71/1.17  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_135])).
% 1.71/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.17  
% 1.71/1.17  Inference rules
% 1.71/1.17  ----------------------
% 1.71/1.17  #Ref     : 0
% 1.71/1.17  #Sup     : 23
% 1.71/1.17  #Fact    : 0
% 1.71/1.17  #Define  : 0
% 1.71/1.17  #Split   : 0
% 1.71/1.17  #Chain   : 0
% 1.71/1.17  #Close   : 0
% 1.71/1.17  
% 1.71/1.17  Ordering : KBO
% 1.71/1.17  
% 1.71/1.17  Simplification rules
% 1.71/1.17  ----------------------
% 1.71/1.17  #Subsume      : 0
% 1.71/1.17  #Demod        : 14
% 1.71/1.17  #Tautology    : 14
% 1.71/1.17  #SimpNegUnit  : 1
% 1.71/1.17  #BackRed      : 2
% 1.71/1.17  
% 1.71/1.17  #Partial instantiations: 0
% 1.71/1.17  #Strategies tried      : 1
% 1.71/1.17  
% 1.71/1.17  Timing (in seconds)
% 1.71/1.17  ----------------------
% 1.71/1.17  Preprocessing        : 0.28
% 1.71/1.17  Parsing              : 0.15
% 1.71/1.17  CNF conversion       : 0.02
% 1.71/1.17  Main loop            : 0.12
% 1.71/1.17  Inferencing          : 0.04
% 1.71/1.17  Reduction            : 0.04
% 1.71/1.17  Demodulation         : 0.03
% 1.71/1.17  BG Simplification    : 0.01
% 1.71/1.17  Subsumption          : 0.02
% 1.71/1.17  Abstraction          : 0.01
% 1.71/1.17  MUC search           : 0.00
% 1.71/1.17  Cooper               : 0.00
% 1.71/1.17  Total                : 0.43
% 1.71/1.17  Index Insertion      : 0.00
% 1.71/1.17  Index Deletion       : 0.00
% 1.71/1.17  Index Matching       : 0.00
% 1.71/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
