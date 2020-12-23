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

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 103 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_struct_0 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_31,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_struct_0(A_4) = k1_xboole_0
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_9] :
      ( k1_struct_0(A_9) = '#skF_2'
      | ~ l1_struct_0(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12])).

tff(c_48,plain,(
    k1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_xboole_0(k1_struct_0(A_6))
      | ~ l1_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,
    ( v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_56,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52])).

tff(c_20,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_6])).

tff(c_64,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ m1_setfam_1(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,'#skF_2')
      | ~ m1_setfam_1('#skF_2',A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_29,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ r1_tarski(A_1,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_4])).

tff(c_82,plain,(
    ! [A_18] :
      ( A_18 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_18) ) ),
    inference(resolution,[status(thm)],[c_73,c_29])).

tff(c_86,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_82])).

tff(c_14,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_14])).

tff(c_96,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_56,c_92])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_struct_0 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.16  
% 1.77/1.16  %Foreground sorts:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Background operators:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Foreground operators:
% 1.77/1.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.77/1.16  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.16  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.77/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.77/1.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.16  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.77/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.77/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.77/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.16  
% 1.77/1.17  tff(f_65, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.77/1.17  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 1.77/1.17  tff(f_51, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 1.77/1.17  tff(f_31, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.77/1.17  tff(f_35, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.77/1.17  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.77/1.17  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.77/1.17  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.77/1.17  tff(c_24, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.77/1.17  tff(c_18, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.77/1.17  tff(c_12, plain, (![A_4]: (k1_struct_0(A_4)=k1_xboole_0 | ~l1_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.17  tff(c_44, plain, (![A_9]: (k1_struct_0(A_9)='#skF_2' | ~l1_struct_0(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12])).
% 1.77/1.17  tff(c_48, plain, (k1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_44])).
% 1.77/1.17  tff(c_16, plain, (![A_6]: (v1_xboole_0(k1_struct_0(A_6)) | ~l1_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.77/1.17  tff(c_52, plain, (v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48, c_16])).
% 1.77/1.17  tff(c_56, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52])).
% 1.77/1.17  tff(c_20, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.77/1.17  tff(c_6, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.17  tff(c_28, plain, (k3_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_6])).
% 1.77/1.17  tff(c_64, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~m1_setfam_1(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.17  tff(c_73, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~m1_setfam_1('#skF_2', A_17))), inference(superposition, [status(thm), theory('equality')], [c_28, c_64])).
% 1.77/1.17  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.77/1.17  tff(c_29, plain, (![A_1]: (A_1='#skF_2' | ~r1_tarski(A_1, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_4])).
% 1.77/1.17  tff(c_82, plain, (![A_18]: (A_18='#skF_2' | ~m1_setfam_1('#skF_2', A_18))), inference(resolution, [status(thm)], [c_73, c_29])).
% 1.77/1.17  tff(c_86, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_82])).
% 1.77/1.17  tff(c_14, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.17  tff(c_92, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_86, c_14])).
% 1.77/1.17  tff(c_96, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_56, c_92])).
% 1.77/1.17  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_96])).
% 1.77/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  Inference rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Ref     : 0
% 1.77/1.17  #Sup     : 19
% 1.77/1.17  #Fact    : 0
% 1.77/1.17  #Define  : 0
% 1.77/1.17  #Split   : 0
% 1.77/1.17  #Chain   : 0
% 1.77/1.17  #Close   : 0
% 1.77/1.17  
% 1.77/1.17  Ordering : KBO
% 1.77/1.17  
% 1.77/1.17  Simplification rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Subsume      : 0
% 1.77/1.17  #Demod        : 11
% 1.77/1.17  #Tautology    : 11
% 1.77/1.17  #SimpNegUnit  : 1
% 1.77/1.17  #BackRed      : 2
% 1.77/1.17  
% 1.77/1.17  #Partial instantiations: 0
% 1.77/1.17  #Strategies tried      : 1
% 1.77/1.17  
% 1.77/1.17  Timing (in seconds)
% 1.77/1.17  ----------------------
% 1.77/1.17  Preprocessing        : 0.28
% 1.77/1.17  Parsing              : 0.16
% 1.77/1.17  CNF conversion       : 0.02
% 1.77/1.17  Main loop            : 0.11
% 1.77/1.17  Inferencing          : 0.04
% 1.77/1.17  Reduction            : 0.03
% 1.77/1.17  Demodulation         : 0.02
% 1.77/1.17  BG Simplification    : 0.01
% 1.77/1.17  Subsumption          : 0.01
% 1.77/1.17  Abstraction          : 0.00
% 1.77/1.17  MUC search           : 0.00
% 1.77/1.17  Cooper               : 0.00
% 1.77/1.17  Total                : 0.42
% 1.77/1.17  Index Insertion      : 0.00
% 1.77/1.17  Index Deletion       : 0.00
% 1.77/1.17  Index Matching       : 0.00
% 1.77/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
