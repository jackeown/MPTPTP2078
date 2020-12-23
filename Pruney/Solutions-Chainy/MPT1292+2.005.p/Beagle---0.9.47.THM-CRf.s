%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   48 (  60 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  94 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_30,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_20])).

tff(c_75,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,k3_tarski(B_25))
      | ~ m1_setfam_1(B_25,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,'#skF_4')
      | ~ m1_setfam_1('#skF_4',A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_75])).

tff(c_102,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_2'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_34,B_35] :
      ( ~ v1_xboole_0(A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_114,c_14])).

tff(c_136,plain,(
    ! [A_24] :
      ( A_24 = '#skF_4'
      | ~ v1_xboole_0('#skF_4')
      | ~ m1_setfam_1('#skF_4',A_24) ) ),
    inference(resolution,[status(thm)],[c_81,c_130])).

tff(c_150,plain,(
    ! [A_41] :
      ( A_41 = '#skF_4'
      | ~ m1_setfam_1('#skF_4',A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_136])).

tff(c_170,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_26,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_184,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_26])).

tff(c_188,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_39,c_184])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:00:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.94/1.20  
% 1.94/1.20  %Foreground sorts:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Background operators:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Foreground operators:
% 1.94/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.20  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.94/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.94/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.20  
% 1.94/1.21  tff(f_72, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.94/1.21  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.21  tff(f_46, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.94/1.21  tff(f_50, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.94/1.21  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.94/1.21  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.21  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.94/1.21  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.21  tff(c_34, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.21  tff(c_28, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.21  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.21  tff(c_39, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 1.94/1.21  tff(c_30, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.21  tff(c_20, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.21  tff(c_37, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_20])).
% 1.94/1.21  tff(c_75, plain, (![A_24, B_25]: (r1_tarski(A_24, k3_tarski(B_25)) | ~m1_setfam_1(B_25, A_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.94/1.21  tff(c_81, plain, (![A_24]: (r1_tarski(A_24, '#skF_4') | ~m1_setfam_1('#skF_4', A_24))), inference(superposition, [status(thm), theory('equality')], [c_37, c_75])).
% 1.94/1.21  tff(c_102, plain, (![A_30, B_31]: (r2_hidden('#skF_2'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.21  tff(c_114, plain, (![A_34, B_35]: (~v1_xboole_0(A_34) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_102, c_2])).
% 1.94/1.21  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.21  tff(c_130, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_114, c_14])).
% 1.94/1.21  tff(c_136, plain, (![A_24]: (A_24='#skF_4' | ~v1_xboole_0('#skF_4') | ~m1_setfam_1('#skF_4', A_24))), inference(resolution, [status(thm)], [c_81, c_130])).
% 1.94/1.21  tff(c_150, plain, (![A_41]: (A_41='#skF_4' | ~m1_setfam_1('#skF_4', A_41))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_136])).
% 1.94/1.21  tff(c_170, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_30, c_150])).
% 1.94/1.21  tff(c_26, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.21  tff(c_184, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_170, c_26])).
% 1.94/1.21  tff(c_188, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_39, c_184])).
% 1.94/1.21  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_188])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 33
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 0
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 1
% 1.94/1.21  #Demod        : 14
% 1.94/1.21  #Tautology    : 16
% 1.94/1.21  #SimpNegUnit  : 1
% 1.94/1.21  #BackRed      : 2
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.29
% 1.94/1.21  Parsing              : 0.16
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.16
% 1.94/1.21  Inferencing          : 0.06
% 1.94/1.21  Reduction            : 0.05
% 1.94/1.21  Demodulation         : 0.03
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.03
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.47
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
