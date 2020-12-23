%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:59 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  74 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_82,plain,(
    ! [C_37,A_38,B_39] :
      ( m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(B_39)))
      | ~ m1_pre_topc(B_39,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_23,c_82])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(u1_struct_0(B_45),u1_struct_0(A_46))
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_113,c_10])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_18,c_34])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_zfmisc_1(A_4),k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_34,B_35,A_36] :
      ( r1_tarski(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,k1_zfmisc_1(A_36))
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_80,plain,(
    ! [B_35] :
      ( r1_tarski('#skF_3',k1_zfmisc_1(B_35))
      | ~ r1_tarski(u1_struct_0('#skF_2'),B_35) ) ),
    inference(resolution,[status(thm)],[c_41,c_68])).

tff(c_134,plain,(
    ! [A_47] :
      ( r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc('#skF_2',A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_121,c_80])).

tff(c_44,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_16])).

tff(c_141,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_52])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.24  
% 1.91/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.25  %$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.91/1.25  
% 1.91/1.25  %Foreground sorts:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Background operators:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Foreground operators:
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.91/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.25  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.91/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.91/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.25  
% 1.91/1.26  tff(f_64, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 1.91/1.26  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.91/1.26  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.91/1.26  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 1.91/1.26  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.91/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.91/1.26  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.91/1.26  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.91/1.26  tff(c_20, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.91/1.26  tff(c_6, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.26  tff(c_8, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.26  tff(c_23, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.91/1.26  tff(c_82, plain, (![C_37, A_38, B_39]: (m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(B_39))) | ~m1_pre_topc(B_39, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.26  tff(c_113, plain, (![B_43, A_44]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_23, c_82])).
% 1.91/1.26  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.26  tff(c_121, plain, (![B_45, A_46]: (r1_tarski(u1_struct_0(B_45), u1_struct_0(A_46)) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_113, c_10])).
% 1.91/1.26  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.91/1.26  tff(c_34, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.26  tff(c_41, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_34])).
% 1.91/1.26  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k1_zfmisc_1(A_4), k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.26  tff(c_54, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.26  tff(c_68, plain, (![A_34, B_35, A_36]: (r1_tarski(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, k1_zfmisc_1(A_36)) | ~r1_tarski(A_36, B_35))), inference(resolution, [status(thm)], [c_4, c_54])).
% 1.91/1.26  tff(c_80, plain, (![B_35]: (r1_tarski('#skF_3', k1_zfmisc_1(B_35)) | ~r1_tarski(u1_struct_0('#skF_2'), B_35))), inference(resolution, [status(thm)], [c_41, c_68])).
% 1.91/1.26  tff(c_134, plain, (![A_47]: (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc('#skF_2', A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_121, c_80])).
% 1.91/1.26  tff(c_44, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.26  tff(c_16, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.91/1.26  tff(c_52, plain, (~r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_16])).
% 1.91/1.26  tff(c_141, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_134, c_52])).
% 1.91/1.26  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_141])).
% 1.91/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  Inference rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Ref     : 0
% 1.91/1.26  #Sup     : 28
% 1.91/1.26  #Fact    : 0
% 1.91/1.26  #Define  : 0
% 1.91/1.26  #Split   : 1
% 1.91/1.26  #Chain   : 0
% 1.91/1.26  #Close   : 0
% 1.91/1.26  
% 1.91/1.26  Ordering : KBO
% 1.91/1.26  
% 1.91/1.26  Simplification rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Subsume      : 3
% 1.91/1.26  #Demod        : 4
% 1.91/1.26  #Tautology    : 5
% 1.91/1.26  #SimpNegUnit  : 0
% 1.91/1.26  #BackRed      : 0
% 1.91/1.26  
% 1.91/1.26  #Partial instantiations: 0
% 1.91/1.26  #Strategies tried      : 1
% 1.91/1.26  
% 1.91/1.26  Timing (in seconds)
% 1.91/1.26  ----------------------
% 2.07/1.26  Preprocessing        : 0.27
% 2.07/1.26  Parsing              : 0.15
% 2.07/1.26  CNF conversion       : 0.02
% 2.07/1.26  Main loop            : 0.16
% 2.07/1.26  Inferencing          : 0.05
% 2.07/1.26  Reduction            : 0.04
% 2.07/1.26  Demodulation         : 0.03
% 2.07/1.26  BG Simplification    : 0.01
% 2.07/1.26  Subsumption          : 0.04
% 2.07/1.26  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.45
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
