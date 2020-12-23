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
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   48 (  60 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  96 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_85,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_28,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | k3_tarski(A_9) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | k3_tarski(A_25) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_27] :
      ( ~ r1_tarski(A_27,'#skF_1'(A_27))
      | k3_tarski(A_27) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_85,c_16])).

tff(c_96,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,k3_tarski(B_5))
      | ~ m1_setfam_1(B_5,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_158,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,'#skF_3')
      | ~ m1_setfam_1('#skF_3',A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_132,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_172,plain,(
    ! [A_33] :
      ( A_33 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_33) ) ),
    inference(resolution,[status(thm)],[c_158,c_144])).

tff(c_188,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_172])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_195,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_18])).

tff(c_199,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40,c_195])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
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
% 1.71/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.16  tff('#skF_3', type, '#skF_3': $i).
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
% 1.91/1.17  tff(f_85, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.91/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.91/1.17  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.91/1.17  tff(f_71, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 1.91/1.17  tff(f_43, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.91/1.17  tff(f_38, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.91/1.17  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.91/1.17  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.91/1.17  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.17  tff(c_32, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.17  tff(c_26, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.91/1.17  tff(c_40, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2])).
% 1.91/1.17  tff(c_28, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.17  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.17  tff(c_38, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 1.91/1.17  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | k3_tarski(A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.17  tff(c_85, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | k3_tarski(A_25)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 1.91/1.17  tff(c_16, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.17  tff(c_91, plain, (![A_27]: (~r1_tarski(A_27, '#skF_1'(A_27)) | k3_tarski(A_27)='#skF_3')), inference(resolution, [status(thm)], [c_85, c_16])).
% 1.91/1.17  tff(c_96, plain, (k3_tarski('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_38, c_91])).
% 1.91/1.17  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(A_4, k3_tarski(B_5)) | ~m1_setfam_1(B_5, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.17  tff(c_158, plain, (![A_32]: (r1_tarski(A_32, '#skF_3') | ~m1_setfam_1('#skF_3', A_32))), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 1.91/1.17  tff(c_132, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.17  tff(c_144, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_132])).
% 1.91/1.17  tff(c_172, plain, (![A_33]: (A_33='#skF_3' | ~m1_setfam_1('#skF_3', A_33))), inference(resolution, [status(thm)], [c_158, c_144])).
% 1.91/1.17  tff(c_188, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_172])).
% 1.91/1.17  tff(c_18, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.17  tff(c_195, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_188, c_18])).
% 1.91/1.17  tff(c_199, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40, c_195])).
% 1.91/1.17  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_199])).
% 1.91/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.17  
% 1.91/1.17  Inference rules
% 1.91/1.17  ----------------------
% 1.91/1.17  #Ref     : 0
% 1.91/1.17  #Sup     : 35
% 1.91/1.17  #Fact    : 0
% 1.91/1.17  #Define  : 0
% 1.91/1.17  #Split   : 0
% 1.91/1.17  #Chain   : 0
% 1.91/1.17  #Close   : 0
% 1.91/1.17  
% 1.91/1.17  Ordering : KBO
% 1.91/1.17  
% 1.91/1.17  Simplification rules
% 1.91/1.17  ----------------------
% 1.91/1.17  #Subsume      : 0
% 1.91/1.17  #Demod        : 20
% 1.91/1.17  #Tautology    : 22
% 1.91/1.17  #SimpNegUnit  : 1
% 1.91/1.17  #BackRed      : 2
% 1.91/1.17  
% 1.91/1.17  #Partial instantiations: 0
% 1.91/1.17  #Strategies tried      : 1
% 1.91/1.17  
% 1.91/1.17  Timing (in seconds)
% 1.91/1.17  ----------------------
% 1.91/1.17  Preprocessing        : 0.28
% 1.91/1.17  Parsing              : 0.15
% 1.91/1.17  CNF conversion       : 0.02
% 1.91/1.17  Main loop            : 0.13
% 1.91/1.17  Inferencing          : 0.05
% 1.91/1.17  Reduction            : 0.04
% 1.91/1.17  Demodulation         : 0.03
% 1.91/1.17  BG Simplification    : 0.01
% 1.91/1.17  Subsumption          : 0.02
% 1.91/1.17  Abstraction          : 0.01
% 1.91/1.17  MUC search           : 0.00
% 1.91/1.17  Cooper               : 0.00
% 1.91/1.17  Total                : 0.44
% 1.91/1.17  Index Insertion      : 0.00
% 1.91/1.17  Index Deletion       : 0.00
% 1.91/1.17  Index Matching       : 0.00
% 1.91/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
