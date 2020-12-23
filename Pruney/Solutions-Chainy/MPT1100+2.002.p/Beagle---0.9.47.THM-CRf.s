%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:28 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  53 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_28,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_60,plain,(
    ! [A_25,B_26] :
      ( k5_setfam_1(A_25,B_26) = k3_tarski(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_25] : k5_setfam_1(A_25,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_66,plain,(
    ! [A_25] : k5_setfam_1(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_105,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_38),B_39),u1_pre_topc(A_38))
      | ~ r1_tarski(B_39,u1_pre_topc(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38))))
      | ~ v2_pre_topc(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_109,plain,(
    ! [A_38] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_38))
      | ~ r1_tarski(k1_xboole_0,u1_pre_topc(A_38))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38))))
      | ~ v2_pre_topc(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_105])).

tff(c_112,plain,(
    ! [A_40] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_40))
      | ~ v2_pre_topc(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2,c_109])).

tff(c_48,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_115,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_48])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.25  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.10/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.25  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.10/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.25  
% 2.10/1.26  tff(f_72, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_pre_topc)).
% 2.10/1.26  tff(f_30, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.10/1.26  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.26  tff(f_28, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.10/1.26  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.10/1.26  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.10/1.26  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.26  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.26  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.10/1.26  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.26  tff(c_4, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.10/1.26  tff(c_60, plain, (![A_25, B_26]: (k5_setfam_1(A_25, B_26)=k3_tarski(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.26  tff(c_64, plain, (![A_25]: (k5_setfam_1(A_25, k1_xboole_0)=k3_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_60])).
% 2.10/1.26  tff(c_66, plain, (![A_25]: (k5_setfam_1(A_25, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 2.10/1.26  tff(c_105, plain, (![A_38, B_39]: (r2_hidden(k5_setfam_1(u1_struct_0(A_38), B_39), u1_pre_topc(A_38)) | ~r1_tarski(B_39, u1_pre_topc(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38)))) | ~v2_pre_topc(A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.10/1.26  tff(c_109, plain, (![A_38]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_38)) | ~r1_tarski(k1_xboole_0, u1_pre_topc(A_38)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38)))) | ~v2_pre_topc(A_38) | ~l1_pre_topc(A_38))), inference(superposition, [status(thm), theory('equality')], [c_66, c_105])).
% 2.10/1.26  tff(c_112, plain, (![A_40]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_40)) | ~v2_pre_topc(A_40) | ~l1_pre_topc(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2, c_109])).
% 2.10/1.26  tff(c_48, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.26  tff(c_115, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_112, c_48])).
% 2.10/1.26  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_115])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 14
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 0
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 0
% 2.10/1.26  #Demod        : 5
% 2.10/1.26  #Tautology    : 6
% 2.10/1.26  #SimpNegUnit  : 0
% 2.10/1.26  #BackRed      : 0
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.10/1.26  Preprocessing        : 0.31
% 2.10/1.26  Parsing              : 0.16
% 2.10/1.26  CNF conversion       : 0.02
% 2.10/1.26  Main loop            : 0.14
% 2.10/1.26  Inferencing          : 0.05
% 2.10/1.26  Reduction            : 0.04
% 2.10/1.26  Demodulation         : 0.03
% 2.10/1.26  BG Simplification    : 0.01
% 2.10/1.26  Subsumption          : 0.03
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.47
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
