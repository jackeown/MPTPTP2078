%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  88 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

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

tff(f_67,negated_conjecture,(
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

tff(f_27,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2])).

tff(c_20,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_29,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_4])).

tff(c_6,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [A_1] : m1_subset_1('#skF_2',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_41,plain,(
    ! [A_13,B_14] :
      ( k5_setfam_1(A_13,B_14) = k3_tarski(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_13] : k5_setfam_1(A_13,'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_27,c_41])).

tff(c_47,plain,(
    ! [A_13] : k5_setfam_1(A_13,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_45])).

tff(c_69,plain,(
    ! [A_24,B_25] :
      ( k5_setfam_1(A_24,B_25) = A_24
      | ~ m1_setfam_1(B_25,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [A_24] :
      ( k5_setfam_1(A_24,'#skF_2') = A_24
      | ~ m1_setfam_1('#skF_2',A_24) ) ),
    inference(resolution,[status(thm)],[c_27,c_69])).

tff(c_76,plain,(
    ! [A_26] :
      ( A_26 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_73])).

tff(c_84,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_16])).

tff(c_94,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30,c_90])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  %$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.14  
% 1.63/1.14  %Foreground sorts:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Background operators:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Foreground operators:
% 1.63/1.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.14  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.63/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.63/1.14  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.63/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.14  
% 1.63/1.15  tff(f_67, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.63/1.15  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.63/1.15  tff(f_27, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.63/1.15  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.63/1.15  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 1.63/1.15  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 1.63/1.15  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.63/1.15  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.63/1.15  tff(c_24, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.63/1.15  tff(c_18, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.63/1.15  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.63/1.15  tff(c_30, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2])).
% 1.63/1.15  tff(c_20, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.63/1.15  tff(c_4, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.15  tff(c_29, plain, (k3_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_4])).
% 1.63/1.15  tff(c_6, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.15  tff(c_27, plain, (![A_1]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6])).
% 1.63/1.15  tff(c_41, plain, (![A_13, B_14]: (k5_setfam_1(A_13, B_14)=k3_tarski(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.15  tff(c_45, plain, (![A_13]: (k5_setfam_1(A_13, '#skF_2')=k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_27, c_41])).
% 1.63/1.15  tff(c_47, plain, (![A_13]: (k5_setfam_1(A_13, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_45])).
% 1.63/1.15  tff(c_69, plain, (![A_24, B_25]: (k5_setfam_1(A_24, B_25)=A_24 | ~m1_setfam_1(B_25, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.63/1.15  tff(c_73, plain, (![A_24]: (k5_setfam_1(A_24, '#skF_2')=A_24 | ~m1_setfam_1('#skF_2', A_24))), inference(resolution, [status(thm)], [c_27, c_69])).
% 1.63/1.15  tff(c_76, plain, (![A_26]: (A_26='#skF_2' | ~m1_setfam_1('#skF_2', A_26))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_73])).
% 1.63/1.15  tff(c_84, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_76])).
% 1.63/1.15  tff(c_16, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.15  tff(c_90, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84, c_16])).
% 1.63/1.15  tff(c_94, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30, c_90])).
% 1.63/1.15  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_94])).
% 1.63/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  Inference rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Ref     : 0
% 1.63/1.15  #Sup     : 15
% 1.63/1.15  #Fact    : 0
% 1.63/1.15  #Define  : 0
% 1.63/1.15  #Split   : 0
% 1.63/1.15  #Chain   : 0
% 1.63/1.15  #Close   : 0
% 1.63/1.15  
% 1.63/1.15  Ordering : KBO
% 1.63/1.15  
% 1.63/1.15  Simplification rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Subsume      : 0
% 1.63/1.15  #Demod        : 12
% 1.63/1.15  #Tautology    : 10
% 1.63/1.15  #SimpNegUnit  : 1
% 1.63/1.15  #BackRed      : 1
% 1.63/1.15  
% 1.63/1.15  #Partial instantiations: 0
% 1.63/1.15  #Strategies tried      : 1
% 1.63/1.15  
% 1.63/1.15  Timing (in seconds)
% 1.63/1.15  ----------------------
% 1.63/1.15  Preprocessing        : 0.27
% 1.63/1.15  Parsing              : 0.15
% 1.63/1.15  CNF conversion       : 0.02
% 1.63/1.15  Main loop            : 0.10
% 1.63/1.15  Inferencing          : 0.04
% 1.63/1.15  Reduction            : 0.03
% 1.63/1.15  Demodulation         : 0.03
% 1.63/1.15  BG Simplification    : 0.01
% 1.63/1.15  Subsumption          : 0.01
% 1.63/1.15  Abstraction          : 0.00
% 1.63/1.15  MUC search           : 0.00
% 1.63/1.15  Cooper               : 0.00
% 1.63/1.15  Total                : 0.39
% 1.63/1.15  Index Insertion      : 0.00
% 1.63/1.15  Index Deletion       : 0.00
% 1.63/1.15  Index Matching       : 0.00
% 1.63/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
