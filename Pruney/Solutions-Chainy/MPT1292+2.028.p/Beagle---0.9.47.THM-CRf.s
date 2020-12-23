%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:33 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   51 (  62 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  83 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_41,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_32,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_6])).

tff(c_20,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_20])).

tff(c_58,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,k3_tarski(B_41))
      | ~ m1_setfam_1(B_41,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_2')
      | ~ m1_setfam_1('#skF_2',A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_58])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_69,plain,(
    ! [A_42] :
      ( k3_xboole_0(A_42,'#skF_2') = A_42
      | ~ m1_setfam_1('#skF_2',A_42) ) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_72,plain,(
    ! [A_43] :
      ( A_43 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_69])).

tff(c_76,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_97,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_97])).

tff(c_102,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41,c_100])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.18  
% 1.94/1.18  %Foreground sorts:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Background operators:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Foreground operators:
% 1.94/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.94/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.18  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.94/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.94/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.94/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.94/1.18  
% 1.94/1.19  tff(f_73, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.94/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.19  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.94/1.19  tff(f_45, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.94/1.19  tff(f_49, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.94/1.19  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.94/1.19  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.94/1.19  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.19  tff(c_36, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.19  tff(c_30, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.19  tff(c_41, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2])).
% 1.94/1.19  tff(c_32, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.94/1.19  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.19  tff(c_40, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_6])).
% 1.94/1.19  tff(c_20, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.19  tff(c_39, plain, (k3_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_20])).
% 1.94/1.19  tff(c_58, plain, (![A_40, B_41]: (r1_tarski(A_40, k3_tarski(B_41)) | ~m1_setfam_1(B_41, A_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.19  tff(c_66, plain, (![A_42]: (r1_tarski(A_42, '#skF_2') | ~m1_setfam_1('#skF_2', A_42))), inference(superposition, [status(thm), theory('equality')], [c_39, c_58])).
% 1.94/1.19  tff(c_4, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.94/1.19  tff(c_69, plain, (![A_42]: (k3_xboole_0(A_42, '#skF_2')=A_42 | ~m1_setfam_1('#skF_2', A_42))), inference(resolution, [status(thm)], [c_66, c_4])).
% 1.94/1.19  tff(c_72, plain, (![A_43]: (A_43='#skF_2' | ~m1_setfam_1('#skF_2', A_43))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_69])).
% 1.94/1.19  tff(c_76, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_72])).
% 1.94/1.19  tff(c_97, plain, (![A_46]: (~v1_xboole_0(u1_struct_0(A_46)) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.19  tff(c_100, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_97])).
% 1.94/1.19  tff(c_102, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_41, c_100])).
% 1.94/1.19  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_102])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 16
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 0
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 0
% 1.94/1.19  #Demod        : 10
% 1.94/1.19  #Tautology    : 11
% 1.94/1.19  #SimpNegUnit  : 1
% 1.94/1.19  #BackRed      : 2
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.20  Preprocessing        : 0.31
% 1.94/1.20  Parsing              : 0.17
% 1.94/1.20  CNF conversion       : 0.02
% 1.94/1.20  Main loop            : 0.11
% 1.94/1.20  Inferencing          : 0.04
% 1.94/1.20  Reduction            : 0.04
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.01
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.44
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
