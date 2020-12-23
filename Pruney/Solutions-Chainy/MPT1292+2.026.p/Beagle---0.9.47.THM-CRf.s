%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:32 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  85 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k4_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_31,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2])).

tff(c_20,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8])).

tff(c_10,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_27,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_10])).

tff(c_50,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_11))
      | ~ m1_setfam_1(B_11,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,'#skF_2')
      | ~ m1_setfam_1('#skF_2',A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_55,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = '#skF_2'
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_58,plain,(
    ! [A_10] :
      ( k4_xboole_0(A_10,'#skF_2') = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_10) ) ),
    inference(resolution,[status(thm)],[c_53,c_55])).

tff(c_65,plain,(
    ! [A_15] :
      ( A_15 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_58])).

tff(c_69,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_16,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_16])).

tff(c_79,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_31,c_75])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.24  
% 1.78/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.24  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k4_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.78/1.24  
% 1.78/1.24  %Foreground sorts:
% 1.78/1.24  
% 1.78/1.24  
% 1.78/1.24  %Background operators:
% 1.78/1.24  
% 1.78/1.24  
% 1.78/1.24  %Foreground operators:
% 1.78/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.78/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.24  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.78/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.78/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.78/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.78/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.24  
% 1.78/1.25  tff(f_59, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.78/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.78/1.25  tff(f_32, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.78/1.25  tff(f_33, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.78/1.25  tff(f_37, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.78/1.25  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.78/1.25  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.78/1.25  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.78/1.25  tff(c_24, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.78/1.25  tff(c_18, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.78/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.78/1.25  tff(c_31, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2])).
% 1.78/1.25  tff(c_20, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.78/1.25  tff(c_8, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.78/1.25  tff(c_28, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8])).
% 1.78/1.25  tff(c_10, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.25  tff(c_27, plain, (k3_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_10])).
% 1.78/1.25  tff(c_50, plain, (![A_10, B_11]: (r1_tarski(A_10, k3_tarski(B_11)) | ~m1_setfam_1(B_11, A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.78/1.25  tff(c_53, plain, (![A_10]: (r1_tarski(A_10, '#skF_2') | ~m1_setfam_1('#skF_2', A_10))), inference(superposition, [status(thm), theory('equality')], [c_27, c_50])).
% 1.78/1.25  tff(c_6, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.78/1.25  tff(c_55, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)='#skF_2' | ~r1_tarski(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6])).
% 1.78/1.25  tff(c_58, plain, (![A_10]: (k4_xboole_0(A_10, '#skF_2')='#skF_2' | ~m1_setfam_1('#skF_2', A_10))), inference(resolution, [status(thm)], [c_53, c_55])).
% 1.78/1.25  tff(c_65, plain, (![A_15]: (A_15='#skF_2' | ~m1_setfam_1('#skF_2', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_58])).
% 1.78/1.25  tff(c_69, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_65])).
% 1.78/1.25  tff(c_16, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.25  tff(c_75, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_16])).
% 1.78/1.25  tff(c_79, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_31, c_75])).
% 1.78/1.25  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_79])).
% 1.78/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.25  
% 1.78/1.25  Inference rules
% 1.78/1.25  ----------------------
% 1.78/1.25  #Ref     : 0
% 1.78/1.25  #Sup     : 13
% 1.78/1.25  #Fact    : 0
% 1.78/1.25  #Define  : 0
% 1.78/1.25  #Split   : 0
% 1.78/1.25  #Chain   : 0
% 1.78/1.25  #Close   : 0
% 1.78/1.25  
% 1.78/1.25  Ordering : KBO
% 1.78/1.25  
% 1.78/1.25  Simplification rules
% 1.78/1.25  ----------------------
% 1.78/1.25  #Subsume      : 0
% 1.78/1.25  #Demod        : 11
% 1.78/1.25  #Tautology    : 7
% 1.78/1.25  #SimpNegUnit  : 1
% 1.78/1.26  #BackRed      : 2
% 1.78/1.26  
% 1.78/1.26  #Partial instantiations: 0
% 1.78/1.26  #Strategies tried      : 1
% 1.78/1.26  
% 1.78/1.26  Timing (in seconds)
% 1.78/1.26  ----------------------
% 1.78/1.26  Preprocessing        : 0.29
% 1.78/1.26  Parsing              : 0.16
% 1.78/1.26  CNF conversion       : 0.02
% 1.78/1.26  Main loop            : 0.09
% 1.78/1.26  Inferencing          : 0.03
% 1.78/1.26  Reduction            : 0.03
% 1.78/1.26  Demodulation         : 0.02
% 1.78/1.26  BG Simplification    : 0.01
% 1.78/1.26  Subsumption          : 0.01
% 1.78/1.26  Abstraction          : 0.00
% 1.78/1.26  MUC search           : 0.00
% 1.78/1.26  Cooper               : 0.00
% 1.78/1.26  Total                : 0.41
% 1.78/1.26  Index Insertion      : 0.00
% 1.78/1.26  Index Deletion       : 0.00
% 1.78/1.26  Index Matching       : 0.00
% 1.78/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
