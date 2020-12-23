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
% DateTime   : Thu Dec  3 10:24:06 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 125 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( m1_connsp_2(B,A,C)
                 => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(k1_tops_1(A_31,B_32),B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_53,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_50])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_61,plain,(
    ! [B_37,A_38,C_39] :
      ( r2_hidden(B_37,k1_tops_1(A_38,C_39))
      | ~ m1_connsp_2(C_39,A_38,B_37)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(B_37,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    ! [B_37] :
      ( r2_hidden(B_37,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_37)
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_66,plain,(
    ! [B_37] :
      ( r2_hidden(B_37,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_37)
      | ~ m1_subset_1(B_37,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_63])).

tff(c_68,plain,(
    ! [B_40] :
      ( r2_hidden(B_40,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_40)
      | ~ m1_subset_1(B_40,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_66])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [B_44,B_45] :
      ( r2_hidden(B_44,B_45)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),B_45)
      | ~ m1_connsp_2('#skF_3','#skF_2',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_101,plain,(
    ! [B_46] :
      ( r2_hidden(B_46,'#skF_3')
      | ~ m1_connsp_2('#skF_3','#skF_2',B_46)
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_53,c_93])).

tff(c_104,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_107,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:40:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.87/1.18  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.87/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.18  
% 1.87/1.20  tff(f_74, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 1.87/1.20  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 1.87/1.20  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 1.87/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.87/1.20  tff(c_14, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.87/1.20  tff(c_16, plain, (m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.87/1.20  tff(c_18, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.87/1.20  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.87/1.20  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.87/1.20  tff(c_48, plain, (![A_31, B_32]: (r1_tarski(k1_tops_1(A_31, B_32), B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.20  tff(c_50, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_48])).
% 1.87/1.20  tff(c_53, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_50])).
% 1.87/1.20  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.87/1.20  tff(c_24, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.87/1.20  tff(c_61, plain, (![B_37, A_38, C_39]: (r2_hidden(B_37, k1_tops_1(A_38, C_39)) | ~m1_connsp_2(C_39, A_38, B_37) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(B_37, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.20  tff(c_63, plain, (![B_37]: (r2_hidden(B_37, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_37) | ~m1_subset_1(B_37, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_61])).
% 1.87/1.20  tff(c_66, plain, (![B_37]: (r2_hidden(B_37, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_37) | ~m1_subset_1(B_37, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_63])).
% 1.87/1.20  tff(c_68, plain, (![B_40]: (r2_hidden(B_40, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_40) | ~m1_subset_1(B_40, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_26, c_66])).
% 1.87/1.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.20  tff(c_93, plain, (![B_44, B_45]: (r2_hidden(B_44, B_45) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), B_45) | ~m1_connsp_2('#skF_3', '#skF_2', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_68, c_2])).
% 1.87/1.20  tff(c_101, plain, (![B_46]: (r2_hidden(B_46, '#skF_3') | ~m1_connsp_2('#skF_3', '#skF_2', B_46) | ~m1_subset_1(B_46, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_53, c_93])).
% 1.87/1.20  tff(c_104, plain, (r2_hidden('#skF_4', '#skF_3') | ~m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_101])).
% 1.87/1.20  tff(c_107, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_104])).
% 1.87/1.20  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_107])).
% 1.87/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  Inference rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Ref     : 0
% 1.87/1.20  #Sup     : 16
% 1.87/1.20  #Fact    : 0
% 1.87/1.20  #Define  : 0
% 1.87/1.20  #Split   : 0
% 1.87/1.20  #Chain   : 0
% 1.87/1.20  #Close   : 0
% 1.87/1.20  
% 1.87/1.20  Ordering : KBO
% 1.87/1.20  
% 1.87/1.20  Simplification rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Subsume      : 2
% 1.87/1.20  #Demod        : 5
% 1.87/1.20  #Tautology    : 2
% 1.87/1.20  #SimpNegUnit  : 2
% 1.87/1.20  #BackRed      : 0
% 1.87/1.20  
% 1.87/1.20  #Partial instantiations: 0
% 1.87/1.20  #Strategies tried      : 1
% 1.87/1.20  
% 1.87/1.20  Timing (in seconds)
% 1.87/1.20  ----------------------
% 1.87/1.20  Preprocessing        : 0.27
% 1.87/1.20  Parsing              : 0.15
% 1.87/1.20  CNF conversion       : 0.02
% 1.87/1.20  Main loop            : 0.16
% 1.87/1.20  Inferencing          : 0.07
% 1.87/1.20  Reduction            : 0.04
% 1.87/1.20  Demodulation         : 0.03
% 1.87/1.20  BG Simplification    : 0.01
% 1.87/1.20  Subsumption          : 0.03
% 1.87/1.20  Abstraction          : 0.01
% 1.87/1.20  MUC search           : 0.00
% 1.87/1.20  Cooper               : 0.00
% 1.87/1.20  Total                : 0.46
% 1.87/1.20  Index Insertion      : 0.00
% 1.87/1.20  Index Deletion       : 0.00
% 1.87/1.20  Index Matching       : 0.00
% 1.87/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
