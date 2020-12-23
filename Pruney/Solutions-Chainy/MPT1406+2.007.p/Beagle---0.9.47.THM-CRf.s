%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:35 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   40 (  66 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 170 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_connsp_2(C,A,B)
               => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [C_28,A_29,B_30] :
      ( m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m2_connsp_2(C_28,A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_34])).

tff(c_39,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_36])).

tff(c_50,plain,(
    ! [B_35,A_36,C_37] :
      ( r1_tarski(B_35,k1_tops_1(A_36,C_37))
      | ~ m2_connsp_2(C_37,A_36,B_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    ! [B_35] :
      ( r1_tarski(B_35,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_39,c_50])).

tff(c_72,plain,(
    ! [B_39] :
      ( r1_tarski(B_39,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_52])).

tff(c_78,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_82,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_78])).

tff(c_4,plain,(
    ! [A_4,B_6] :
      ( r1_tarski(k1_tops_1(A_4,B_6),B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_41,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_39,c_4])).

tff(c_44,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_41])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_3')
      | ~ r1_tarski(A_1,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_87,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_47])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:35:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.97/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.97/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.97/1.22  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 1.97/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.22  
% 1.97/1.24  tff(f_79, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_connsp_2)).
% 1.97/1.24  tff(f_63, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 1.97/1.24  tff(f_52, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 1.97/1.24  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 1.97/1.24  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.97/1.24  tff(c_12, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.24  tff(c_14, plain, (m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.24  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.24  tff(c_20, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.24  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.24  tff(c_34, plain, (![C_28, A_29, B_30]: (m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_29))) | ~m2_connsp_2(C_28, A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.24  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_34])).
% 1.97/1.24  tff(c_39, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_36])).
% 1.97/1.24  tff(c_50, plain, (![B_35, A_36, C_37]: (r1_tarski(B_35, k1_tops_1(A_36, C_37)) | ~m2_connsp_2(C_37, A_36, B_35) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.24  tff(c_52, plain, (![B_35]: (r1_tarski(B_35, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_39, c_50])).
% 1.97/1.24  tff(c_72, plain, (![B_39]: (r1_tarski(B_39, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_52])).
% 1.97/1.24  tff(c_78, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_72])).
% 1.97/1.24  tff(c_82, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_78])).
% 1.97/1.24  tff(c_4, plain, (![A_4, B_6]: (r1_tarski(k1_tops_1(A_4, B_6), B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.97/1.24  tff(c_41, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_39, c_4])).
% 1.97/1.24  tff(c_44, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_41])).
% 1.97/1.24  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.24  tff(c_47, plain, (![A_1]: (r1_tarski(A_1, '#skF_3') | ~r1_tarski(A_1, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_2])).
% 1.97/1.24  tff(c_87, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_47])).
% 1.97/1.24  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_87])).
% 1.97/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  Inference rules
% 1.97/1.24  ----------------------
% 1.97/1.24  #Ref     : 0
% 1.97/1.24  #Sup     : 14
% 1.97/1.24  #Fact    : 0
% 1.97/1.24  #Define  : 0
% 1.97/1.24  #Split   : 2
% 1.97/1.24  #Chain   : 0
% 1.97/1.24  #Close   : 0
% 1.97/1.24  
% 1.97/1.24  Ordering : KBO
% 1.97/1.24  
% 1.97/1.24  Simplification rules
% 1.97/1.24  ----------------------
% 1.97/1.24  #Subsume      : 0
% 1.97/1.24  #Demod        : 15
% 1.97/1.24  #Tautology    : 1
% 1.97/1.24  #SimpNegUnit  : 1
% 1.97/1.24  #BackRed      : 0
% 1.97/1.24  
% 1.97/1.24  #Partial instantiations: 0
% 1.97/1.24  #Strategies tried      : 1
% 1.97/1.24  
% 1.97/1.24  Timing (in seconds)
% 1.97/1.24  ----------------------
% 1.97/1.24  Preprocessing        : 0.30
% 1.97/1.24  Parsing              : 0.17
% 1.97/1.24  CNF conversion       : 0.02
% 1.97/1.24  Main loop            : 0.14
% 1.97/1.24  Inferencing          : 0.05
% 1.97/1.24  Reduction            : 0.04
% 1.97/1.24  Demodulation         : 0.03
% 1.97/1.24  BG Simplification    : 0.01
% 1.97/1.24  Subsumption          : 0.03
% 1.97/1.24  Abstraction          : 0.01
% 1.97/1.24  MUC search           : 0.00
% 1.97/1.24  Cooper               : 0.00
% 1.97/1.24  Total                : 0.46
% 1.97/1.24  Index Insertion      : 0.00
% 1.97/1.24  Index Deletion       : 0.00
% 1.97/1.24  Index Matching       : 0.00
% 1.97/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
