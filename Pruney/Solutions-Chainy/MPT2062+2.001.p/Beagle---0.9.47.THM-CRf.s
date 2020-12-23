%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:38 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 138 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C,D] :
            ( ( r1_tarski(B,C)
              & r2_waybel_7(A,B,D) )
           => r2_waybel_7(A,C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow19)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( r2_waybel_7(A,B,C)
        <=> ! [D] :
              ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(D,A)
                  & r2_hidden(C,D) )
               => r2_hidden(D,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    r2_waybel_7('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_6,B_13,C_14] :
      ( v3_pre_topc('#skF_2'(A_6,B_13,C_14),A_6)
      | r2_waybel_7(A_6,B_13,C_14)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_6,B_13,C_14] :
      ( m1_subset_1('#skF_2'(A_6,B_13,C_14),k1_zfmisc_1(u1_struct_0(A_6)))
      | r2_waybel_7(A_6,B_13,C_14)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [C_14,A_6,B_13] :
      ( r2_hidden(C_14,'#skF_2'(A_6,B_13,C_14))
      | r2_waybel_7(A_6,B_13,C_14)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_127,plain,(
    ! [D_67,B_68,C_69,A_70] :
      ( r2_hidden(D_67,B_68)
      | ~ r2_hidden(C_69,D_67)
      | ~ v3_pre_topc(D_67,A_70)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ r2_waybel_7(A_70,B_68,C_69)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_163,plain,(
    ! [A_113,B_110,A_111,B_109,C_112] :
      ( r2_hidden('#skF_2'(A_113,B_109,C_112),B_110)
      | ~ v3_pre_topc('#skF_2'(A_113,B_109,C_112),A_111)
      | ~ m1_subset_1('#skF_2'(A_113,B_109,C_112),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ r2_waybel_7(A_111,B_110,C_112)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | r2_waybel_7(A_113,B_109,C_112)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_167,plain,(
    ! [A_114,B_115,C_116,B_117] :
      ( r2_hidden('#skF_2'(A_114,B_115,C_116),B_117)
      | ~ v3_pre_topc('#skF_2'(A_114,B_115,C_116),A_114)
      | ~ r2_waybel_7(A_114,B_117,C_116)
      | r2_waybel_7(A_114,B_115,C_116)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_16,c_163])).

tff(c_171,plain,(
    ! [A_118,B_119,C_120,B_121] :
      ( r2_hidden('#skF_2'(A_118,B_119,C_120),B_121)
      | ~ r2_waybel_7(A_118,B_121,C_120)
      | r2_waybel_7(A_118,B_119,C_120)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [B_126,B_122,B_125,A_123,C_124] :
      ( r2_hidden('#skF_2'(A_123,B_122,C_124),B_126)
      | ~ r1_tarski(B_125,B_126)
      | ~ r2_waybel_7(A_123,B_125,C_124)
      | r2_waybel_7(A_123,B_122,C_124)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_171,c_2])).

tff(c_193,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_hidden('#skF_2'(A_127,B_128,C_129),'#skF_5')
      | ~ r2_waybel_7(A_127,'#skF_4',C_129)
      | r2_waybel_7(A_127,B_128,C_129)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_22,c_183])).

tff(c_10,plain,(
    ! [A_6,B_13,C_14] :
      ( ~ r2_hidden('#skF_2'(A_6,B_13,C_14),B_13)
      | r2_waybel_7(A_6,B_13,C_14)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_205,plain,(
    ! [A_130,C_131] :
      ( ~ r2_waybel_7(A_130,'#skF_4',C_131)
      | r2_waybel_7(A_130,'#skF_5',C_131)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_193,c_10])).

tff(c_18,plain,(
    ~ r2_waybel_7('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_215,plain,
    ( ~ r2_waybel_7('#skF_3','#skF_4','#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_205,c_18])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.30  %$ r2_waybel_7 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.31/1.30  
% 2.31/1.30  %Foreground sorts:
% 2.31/1.30  
% 2.31/1.30  
% 2.31/1.30  %Background operators:
% 2.31/1.30  
% 2.31/1.30  
% 2.31/1.30  %Foreground operators:
% 2.31/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.31/1.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.31/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.31/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.30  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.31/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.31/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.30  
% 2.31/1.31  tff(f_63, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B, C, D]: ((r1_tarski(B, C) & r2_waybel_7(A, B, D)) => r2_waybel_7(A, C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow19)).
% 2.31/1.31  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (r2_waybel_7(A, B, C) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(D, A) & r2_hidden(C, D)) => r2_hidden(D, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_waybel_7)).
% 2.31/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.31/1.31  tff(c_26, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.31  tff(c_24, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.31  tff(c_20, plain, (r2_waybel_7('#skF_3', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.31  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.31  tff(c_14, plain, (![A_6, B_13, C_14]: (v3_pre_topc('#skF_2'(A_6, B_13, C_14), A_6) | r2_waybel_7(A_6, B_13, C_14) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.31  tff(c_16, plain, (![A_6, B_13, C_14]: (m1_subset_1('#skF_2'(A_6, B_13, C_14), k1_zfmisc_1(u1_struct_0(A_6))) | r2_waybel_7(A_6, B_13, C_14) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.31  tff(c_12, plain, (![C_14, A_6, B_13]: (r2_hidden(C_14, '#skF_2'(A_6, B_13, C_14)) | r2_waybel_7(A_6, B_13, C_14) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.31  tff(c_127, plain, (![D_67, B_68, C_69, A_70]: (r2_hidden(D_67, B_68) | ~r2_hidden(C_69, D_67) | ~v3_pre_topc(D_67, A_70) | ~m1_subset_1(D_67, k1_zfmisc_1(u1_struct_0(A_70))) | ~r2_waybel_7(A_70, B_68, C_69) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.31  tff(c_163, plain, (![A_113, B_110, A_111, B_109, C_112]: (r2_hidden('#skF_2'(A_113, B_109, C_112), B_110) | ~v3_pre_topc('#skF_2'(A_113, B_109, C_112), A_111) | ~m1_subset_1('#skF_2'(A_113, B_109, C_112), k1_zfmisc_1(u1_struct_0(A_111))) | ~r2_waybel_7(A_111, B_110, C_112) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | r2_waybel_7(A_113, B_109, C_112) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(resolution, [status(thm)], [c_12, c_127])).
% 2.31/1.31  tff(c_167, plain, (![A_114, B_115, C_116, B_117]: (r2_hidden('#skF_2'(A_114, B_115, C_116), B_117) | ~v3_pre_topc('#skF_2'(A_114, B_115, C_116), A_114) | ~r2_waybel_7(A_114, B_117, C_116) | r2_waybel_7(A_114, B_115, C_116) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(resolution, [status(thm)], [c_16, c_163])).
% 2.31/1.31  tff(c_171, plain, (![A_118, B_119, C_120, B_121]: (r2_hidden('#skF_2'(A_118, B_119, C_120), B_121) | ~r2_waybel_7(A_118, B_121, C_120) | r2_waybel_7(A_118, B_119, C_120) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(resolution, [status(thm)], [c_14, c_167])).
% 2.31/1.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.31  tff(c_183, plain, (![B_126, B_122, B_125, A_123, C_124]: (r2_hidden('#skF_2'(A_123, B_122, C_124), B_126) | ~r1_tarski(B_125, B_126) | ~r2_waybel_7(A_123, B_125, C_124) | r2_waybel_7(A_123, B_122, C_124) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(resolution, [status(thm)], [c_171, c_2])).
% 2.31/1.31  tff(c_193, plain, (![A_127, B_128, C_129]: (r2_hidden('#skF_2'(A_127, B_128, C_129), '#skF_5') | ~r2_waybel_7(A_127, '#skF_4', C_129) | r2_waybel_7(A_127, B_128, C_129) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(resolution, [status(thm)], [c_22, c_183])).
% 2.31/1.31  tff(c_10, plain, (![A_6, B_13, C_14]: (~r2_hidden('#skF_2'(A_6, B_13, C_14), B_13) | r2_waybel_7(A_6, B_13, C_14) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.31  tff(c_205, plain, (![A_130, C_131]: (~r2_waybel_7(A_130, '#skF_4', C_131) | r2_waybel_7(A_130, '#skF_5', C_131) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130))), inference(resolution, [status(thm)], [c_193, c_10])).
% 2.31/1.31  tff(c_18, plain, (~r2_waybel_7('#skF_3', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.31  tff(c_215, plain, (~r2_waybel_7('#skF_3', '#skF_4', '#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_205, c_18])).
% 2.31/1.31  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_215])).
% 2.31/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.31  
% 2.31/1.31  Inference rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Ref     : 0
% 2.31/1.31  #Sup     : 45
% 2.31/1.31  #Fact    : 0
% 2.31/1.31  #Define  : 0
% 2.31/1.31  #Split   : 1
% 2.31/1.31  #Chain   : 0
% 2.31/1.31  #Close   : 0
% 2.31/1.31  
% 2.31/1.31  Ordering : KBO
% 2.31/1.31  
% 2.31/1.31  Simplification rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Subsume      : 12
% 2.31/1.31  #Demod        : 3
% 2.31/1.31  #Tautology    : 2
% 2.31/1.31  #SimpNegUnit  : 0
% 2.31/1.31  #BackRed      : 0
% 2.31/1.31  
% 2.31/1.31  #Partial instantiations: 0
% 2.31/1.31  #Strategies tried      : 1
% 2.31/1.31  
% 2.31/1.31  Timing (in seconds)
% 2.31/1.31  ----------------------
% 2.31/1.31  Preprocessing        : 0.27
% 2.31/1.31  Parsing              : 0.15
% 2.31/1.31  CNF conversion       : 0.02
% 2.31/1.31  Main loop            : 0.27
% 2.31/1.31  Inferencing          : 0.11
% 2.31/1.31  Reduction            : 0.06
% 2.31/1.31  Demodulation         : 0.04
% 2.31/1.31  BG Simplification    : 0.01
% 2.31/1.31  Subsumption          : 0.07
% 2.31/1.31  Abstraction          : 0.01
% 2.31/1.31  MUC search           : 0.00
% 2.31/1.31  Cooper               : 0.00
% 2.31/1.31  Total                : 0.57
% 2.31/1.31  Index Insertion      : 0.00
% 2.31/1.31  Index Deletion       : 0.00
% 2.31/1.31  Index Matching       : 0.00
% 2.31/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
