%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  91 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_40,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_48,plain,(
    ! [A_20] :
      ( v1_xboole_0(A_20)
      | r2_hidden('#skF_1'(A_20),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [A_21] :
      ( ~ r1_tarski(A_21,'#skF_1'(A_21))
      | v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_48,c_20])).

tff(c_62,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_26,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_33,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_14])).

tff(c_78,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,k3_tarski(B_26))
      | ~ m1_setfam_1(B_26,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,'#skF_3')
      | ~ m1_setfam_1('#skF_3',A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_78])).

tff(c_110,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [A_25] :
      ( A_25 = '#skF_3'
      | ~ r1_tarski('#skF_3',A_25)
      | ~ m1_setfam_1('#skF_3',A_25) ) ),
    inference(resolution,[status(thm)],[c_84,c_110])).

tff(c_145,plain,(
    ! [A_34] :
      ( A_34 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112])).

tff(c_161,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_22,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_22])).

tff(c_172,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_62,c_168])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:08:30 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.70/1.14  
% 1.70/1.14  %Foreground sorts:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Background operators:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Foreground operators:
% 1.70/1.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.70/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.14  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.70/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.70/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.14  
% 1.70/1.15  tff(f_71, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.70/1.15  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.70/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.70/1.15  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.70/1.15  tff(f_40, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.70/1.15  tff(f_44, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.70/1.15  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.70/1.15  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.70/1.15  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.70/1.15  tff(c_30, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.70/1.15  tff(c_24, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.70/1.15  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.15  tff(c_34, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 1.70/1.15  tff(c_48, plain, (![A_20]: (v1_xboole_0(A_20) | r2_hidden('#skF_1'(A_20), A_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.15  tff(c_20, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.70/1.15  tff(c_57, plain, (![A_21]: (~r1_tarski(A_21, '#skF_1'(A_21)) | v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_48, c_20])).
% 1.70/1.15  tff(c_62, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_57])).
% 1.70/1.15  tff(c_26, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.70/1.15  tff(c_14, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.70/1.15  tff(c_33, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_14])).
% 1.70/1.15  tff(c_78, plain, (![A_25, B_26]: (r1_tarski(A_25, k3_tarski(B_26)) | ~m1_setfam_1(B_26, A_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.70/1.15  tff(c_84, plain, (![A_25]: (r1_tarski(A_25, '#skF_3') | ~m1_setfam_1('#skF_3', A_25))), inference(superposition, [status(thm), theory('equality')], [c_33, c_78])).
% 1.70/1.15  tff(c_110, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.15  tff(c_112, plain, (![A_25]: (A_25='#skF_3' | ~r1_tarski('#skF_3', A_25) | ~m1_setfam_1('#skF_3', A_25))), inference(resolution, [status(thm)], [c_84, c_110])).
% 1.70/1.15  tff(c_145, plain, (![A_34]: (A_34='#skF_3' | ~m1_setfam_1('#skF_3', A_34))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_112])).
% 1.70/1.15  tff(c_161, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_145])).
% 1.70/1.15  tff(c_22, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.15  tff(c_168, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_161, c_22])).
% 1.70/1.15  tff(c_172, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_62, c_168])).
% 1.70/1.15  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_172])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 29
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 0
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 0
% 1.70/1.15  #Demod        : 15
% 1.70/1.15  #Tautology    : 18
% 1.70/1.15  #SimpNegUnit  : 1
% 1.70/1.15  #BackRed      : 2
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.15  Timing (in seconds)
% 1.70/1.15  ----------------------
% 1.70/1.16  Preprocessing        : 0.28
% 1.70/1.16  Parsing              : 0.15
% 1.70/1.16  CNF conversion       : 0.02
% 1.70/1.16  Main loop            : 0.13
% 1.70/1.16  Inferencing          : 0.05
% 1.70/1.16  Reduction            : 0.04
% 1.70/1.16  Demodulation         : 0.03
% 1.70/1.16  BG Simplification    : 0.01
% 1.70/1.16  Subsumption          : 0.02
% 1.70/1.16  Abstraction          : 0.01
% 1.70/1.16  MUC search           : 0.00
% 1.70/1.16  Cooper               : 0.00
% 1.70/1.16  Total                : 0.43
% 1.70/1.16  Index Insertion      : 0.00
% 1.70/1.16  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
