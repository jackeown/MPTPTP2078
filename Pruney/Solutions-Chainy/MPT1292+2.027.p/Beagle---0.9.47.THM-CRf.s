%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:32 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   49 (  78 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 ( 121 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_72,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_33,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_42,plain,(
    ! [B_18,A_19] :
      ( m1_setfam_1(B_18,A_19)
      | ~ r1_tarski(A_19,k3_tarski(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51,plain,(
    ! [B_18] : m1_setfam_1(B_18,'#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_42])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_31,plain,(
    ! [A_2] : m1_subset_1('#skF_2',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_59,plain,(
    ! [A_27,B_28] :
      ( k5_setfam_1(A_27,B_28) = k3_tarski(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ! [A_27] : k5_setfam_1(A_27,'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_59])).

tff(c_72,plain,(
    ! [A_30,B_31] :
      ( k5_setfam_1(A_30,B_31) = A_30
      | ~ m1_setfam_1(B_31,A_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [A_30] :
      ( k5_setfam_1(A_30,'#skF_2') = A_30
      | ~ m1_setfam_1('#skF_2',A_30) ) ),
    inference(resolution,[status(thm)],[c_31,c_72])).

tff(c_79,plain,(
    ! [A_32] :
      ( k3_tarski('#skF_2') = A_32
      | ~ m1_setfam_1('#skF_2',A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_76])).

tff(c_87,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_51,c_79])).

tff(c_24,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_88,plain,(
    u1_struct_0('#skF_1') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_101,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_88])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_20])).

tff(c_111,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_34,c_107])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:43:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.22  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.93/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.93/1.22  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.93/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.22  
% 1.93/1.23  tff(f_72, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.93/1.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.93/1.23  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.93/1.23  tff(f_34, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.93/1.23  tff(f_30, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.93/1.23  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 1.93/1.23  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 1.93/1.23  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.93/1.23  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.23  tff(c_28, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.23  tff(c_22, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.93/1.23  tff(c_34, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2])).
% 1.93/1.23  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.93/1.23  tff(c_33, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4])).
% 1.93/1.23  tff(c_42, plain, (![B_18, A_19]: (m1_setfam_1(B_18, A_19) | ~r1_tarski(A_19, k3_tarski(B_18)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.23  tff(c_51, plain, (![B_18]: (m1_setfam_1(B_18, '#skF_2'))), inference(resolution, [status(thm)], [c_33, c_42])).
% 1.93/1.23  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.93/1.23  tff(c_31, plain, (![A_2]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6])).
% 1.93/1.23  tff(c_59, plain, (![A_27, B_28]: (k5_setfam_1(A_27, B_28)=k3_tarski(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.23  tff(c_64, plain, (![A_27]: (k5_setfam_1(A_27, '#skF_2')=k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_31, c_59])).
% 1.93/1.23  tff(c_72, plain, (![A_30, B_31]: (k5_setfam_1(A_30, B_31)=A_30 | ~m1_setfam_1(B_31, A_30) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.23  tff(c_76, plain, (![A_30]: (k5_setfam_1(A_30, '#skF_2')=A_30 | ~m1_setfam_1('#skF_2', A_30))), inference(resolution, [status(thm)], [c_31, c_72])).
% 1.93/1.23  tff(c_79, plain, (![A_32]: (k3_tarski('#skF_2')=A_32 | ~m1_setfam_1('#skF_2', A_32))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_76])).
% 1.93/1.23  tff(c_87, plain, (k3_tarski('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_51, c_79])).
% 1.93/1.23  tff(c_24, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.23  tff(c_88, plain, (u1_struct_0('#skF_1')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_24, c_79])).
% 1.93/1.23  tff(c_101, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_88])).
% 1.93/1.23  tff(c_20, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.23  tff(c_107, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_20])).
% 1.93/1.23  tff(c_111, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_34, c_107])).
% 1.93/1.23  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_111])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 18
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 0
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 0
% 1.93/1.23  #Demod        : 12
% 1.93/1.23  #Tautology    : 10
% 1.93/1.23  #SimpNegUnit  : 1
% 1.93/1.23  #BackRed      : 3
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 1.93/1.24  Preprocessing        : 0.31
% 1.93/1.24  Parsing              : 0.17
% 1.93/1.24  CNF conversion       : 0.02
% 1.93/1.24  Main loop            : 0.11
% 1.93/1.24  Inferencing          : 0.04
% 1.93/1.24  Reduction            : 0.04
% 1.93/1.24  Demodulation         : 0.03
% 1.93/1.24  BG Simplification    : 0.01
% 1.93/1.24  Subsumption          : 0.01
% 1.93/1.24  Abstraction          : 0.00
% 1.93/1.24  MUC search           : 0.00
% 1.93/1.24  Cooper               : 0.00
% 1.93/1.24  Total                : 0.44
% 1.93/1.24  Index Insertion      : 0.00
% 1.93/1.24  Index Deletion       : 0.00
% 1.93/1.24  Index Matching       : 0.00
% 1.93/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
