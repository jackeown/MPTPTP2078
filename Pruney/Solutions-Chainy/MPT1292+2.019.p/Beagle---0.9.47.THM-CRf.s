%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:31 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  89 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

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
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_29,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2])).

tff(c_47,plain,(
    ! [A_10] :
      ( u1_struct_0(A_10) = k2_struct_0(A_10)
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_47])).

tff(c_20,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    m1_setfam_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_20])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_3] : k2_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_8,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_27,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_8])).

tff(c_60,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ m1_setfam_1(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_16] :
      ( r1_tarski(A_16,'#skF_2')
      | ~ m1_setfam_1('#skF_2',A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_60])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    ! [A_16] :
      ( k2_xboole_0(A_16,'#skF_2') = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_16) ) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_82,plain,(
    ! [A_19] :
      ( A_19 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_86,plain,(
    k2_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_82])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_16])).

tff(c_97,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_29,c_93])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:32:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.70/1.12  
% 1.70/1.12  %Foreground sorts:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Background operators:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Foreground operators:
% 1.70/1.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.12  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.70/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.12  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.70/1.12  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.70/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.13  
% 1.70/1.14  tff(f_63, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.70/1.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.70/1.14  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 1.70/1.14  tff(f_32, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.70/1.14  tff(f_33, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.70/1.14  tff(f_37, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.70/1.14  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.70/1.14  tff(f_49, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 1.70/1.14  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.14  tff(c_24, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.14  tff(c_18, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.70/1.14  tff(c_29, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2])).
% 1.70/1.14  tff(c_47, plain, (![A_10]: (u1_struct_0(A_10)=k2_struct_0(A_10) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.70/1.14  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_47])).
% 1.70/1.14  tff(c_20, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.14  tff(c_52, plain, (m1_setfam_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_20])).
% 1.70/1.14  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.70/1.14  tff(c_28, plain, (![A_3]: (k2_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6])).
% 1.70/1.14  tff(c_8, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.14  tff(c_27, plain, (k3_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_8])).
% 1.70/1.14  tff(c_60, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~m1_setfam_1(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.14  tff(c_68, plain, (![A_16]: (r1_tarski(A_16, '#skF_2') | ~m1_setfam_1('#skF_2', A_16))), inference(superposition, [status(thm), theory('equality')], [c_27, c_60])).
% 1.70/1.14  tff(c_4, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.70/1.14  tff(c_71, plain, (![A_16]: (k2_xboole_0(A_16, '#skF_2')='#skF_2' | ~m1_setfam_1('#skF_2', A_16))), inference(resolution, [status(thm)], [c_68, c_4])).
% 1.70/1.14  tff(c_82, plain, (![A_19]: (A_19='#skF_2' | ~m1_setfam_1('#skF_2', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_71])).
% 1.70/1.14  tff(c_86, plain, (k2_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_52, c_82])).
% 1.70/1.14  tff(c_16, plain, (![A_7]: (~v1_xboole_0(k2_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.70/1.14  tff(c_93, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_86, c_16])).
% 1.70/1.14  tff(c_97, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_29, c_93])).
% 1.70/1.14  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_97])).
% 1.70/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  Inference rules
% 1.70/1.14  ----------------------
% 1.70/1.14  #Ref     : 0
% 1.70/1.14  #Sup     : 18
% 1.70/1.14  #Fact    : 0
% 1.70/1.14  #Define  : 0
% 1.70/1.14  #Split   : 0
% 1.70/1.14  #Chain   : 0
% 1.70/1.14  #Close   : 0
% 1.70/1.14  
% 1.70/1.14  Ordering : KBO
% 1.70/1.14  
% 1.70/1.14  Simplification rules
% 1.70/1.14  ----------------------
% 1.70/1.14  #Subsume      : 0
% 1.70/1.14  #Demod        : 12
% 1.70/1.14  #Tautology    : 10
% 1.70/1.14  #SimpNegUnit  : 1
% 1.70/1.14  #BackRed      : 4
% 1.70/1.14  
% 1.70/1.14  #Partial instantiations: 0
% 1.70/1.14  #Strategies tried      : 1
% 1.70/1.14  
% 1.70/1.14  Timing (in seconds)
% 1.70/1.14  ----------------------
% 1.70/1.14  Preprocessing        : 0.28
% 1.70/1.14  Parsing              : 0.15
% 1.70/1.14  CNF conversion       : 0.02
% 1.70/1.14  Main loop            : 0.11
% 1.70/1.14  Inferencing          : 0.04
% 1.70/1.14  Reduction            : 0.04
% 1.70/1.14  Demodulation         : 0.03
% 1.70/1.14  BG Simplification    : 0.01
% 1.70/1.14  Subsumption          : 0.01
% 1.70/1.14  Abstraction          : 0.00
% 1.70/1.14  MUC search           : 0.00
% 1.70/1.14  Cooper               : 0.00
% 1.70/1.14  Total                : 0.42
% 1.70/1.14  Index Insertion      : 0.00
% 1.70/1.14  Index Deletion       : 0.00
% 1.70/1.14  Index Matching       : 0.00
% 1.70/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
