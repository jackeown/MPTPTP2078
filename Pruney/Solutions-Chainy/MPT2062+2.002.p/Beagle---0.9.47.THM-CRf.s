%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:38 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 165 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C,D] :
            ( ( r1_tarski(B,C)
              & r2_waybel_7(A,B,D) )
           => r2_waybel_7(A,C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow19)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    r2_waybel_7('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_7,B_14,C_15] :
      ( v3_pre_topc('#skF_1'(A_7,B_14,C_15),A_7)
      | r2_waybel_7(A_7,B_14,C_15)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_7,B_14,C_15] :
      ( m1_subset_1('#skF_1'(A_7,B_14,C_15),k1_zfmisc_1(u1_struct_0(A_7)))
      | r2_waybel_7(A_7,B_14,C_15)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [C_15,A_7,B_14] :
      ( r2_hidden(C_15,'#skF_1'(A_7,B_14,C_15))
      | r2_waybel_7(A_7,B_14,C_15)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [D_48,B_49,C_50,A_51] :
      ( r2_hidden(D_48,B_49)
      | ~ r2_hidden(C_50,D_48)
      | ~ v3_pre_topc(D_48,A_51)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ r2_waybel_7(A_51,B_49,C_50)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [B_83,B_85,C_87,A_84,A_86] :
      ( r2_hidden('#skF_1'(A_86,B_83,C_87),B_85)
      | ~ v3_pre_topc('#skF_1'(A_86,B_83,C_87),A_84)
      | ~ m1_subset_1('#skF_1'(A_86,B_83,C_87),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ r2_waybel_7(A_84,B_85,C_87)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | r2_waybel_7(A_86,B_83,C_87)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_12,c_58])).

tff(c_113,plain,(
    ! [A_88,B_89,C_90,B_91] :
      ( r2_hidden('#skF_1'(A_88,B_89,C_90),B_91)
      | ~ v3_pre_topc('#skF_1'(A_88,B_89,C_90),A_88)
      | ~ r2_waybel_7(A_88,B_91,C_90)
      | r2_waybel_7(A_88,B_89,C_90)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_117,plain,(
    ! [A_92,B_93,C_94,B_95] :
      ( r2_hidden('#skF_1'(A_92,B_93,C_94),B_95)
      | ~ r2_waybel_7(A_92,B_95,C_94)
      | r2_waybel_7(A_92,B_93,C_94)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_98,C_96,A_99,B_97,B_100] :
      ( r2_hidden('#skF_1'(A_98,B_100,C_96),A_99)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_99))
      | ~ r2_waybel_7(A_98,B_97,C_96)
      | r2_waybel_7(A_98,B_100,C_96)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_136,plain,(
    ! [C_104,A_105,B_102,B_101,A_103] :
      ( r2_hidden('#skF_1'(A_103,B_101,C_104),B_102)
      | ~ r2_waybel_7(A_103,A_105,C_104)
      | r2_waybel_7(A_103,B_101,C_104)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | ~ r1_tarski(A_105,B_102) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_142,plain,(
    ! [B_101,B_102] :
      ( r2_hidden('#skF_1'('#skF_2',B_101,'#skF_5'),B_102)
      | r2_waybel_7('#skF_2',B_101,'#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski('#skF_3',B_102) ) ),
    inference(resolution,[status(thm)],[c_20,c_136])).

tff(c_148,plain,(
    ! [B_106,B_107] :
      ( r2_hidden('#skF_1'('#skF_2',B_106,'#skF_5'),B_107)
      | r2_waybel_7('#skF_2',B_106,'#skF_5')
      | ~ r1_tarski('#skF_3',B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_142])).

tff(c_10,plain,(
    ! [A_7,B_14,C_15] :
      ( ~ r2_hidden('#skF_1'(A_7,B_14,C_15),B_14)
      | r2_waybel_7(A_7,B_14,C_15)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_154,plain,(
    ! [B_107] :
      ( ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | r2_waybel_7('#skF_2',B_107,'#skF_5')
      | ~ r1_tarski('#skF_3',B_107) ) ),
    inference(resolution,[status(thm)],[c_148,c_10])).

tff(c_162,plain,(
    ! [B_108] :
      ( r2_waybel_7('#skF_2',B_108,'#skF_5')
      | ~ r1_tarski('#skF_3',B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_154])).

tff(c_18,plain,(
    ~ r2_waybel_7('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_169,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_18])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.34  %$ r2_waybel_7 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.27/1.34  
% 2.27/1.34  %Foreground sorts:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Background operators:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Foreground operators:
% 2.27/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.27/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.27/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.27/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.34  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.27/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.34  
% 2.27/1.36  tff(f_67, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B, C, D]: ((r1_tarski(B, C) & r2_waybel_7(A, B, D)) => r2_waybel_7(A, C, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow19)).
% 2.27/1.36  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.27/1.36  tff(f_52, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (r2_waybel_7(A, B, C) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(D, A) & r2_hidden(C, D)) => r2_hidden(D, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_waybel_7)).
% 2.27/1.36  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.27/1.36  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.36  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.36  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.36  tff(c_20, plain, (r2_waybel_7('#skF_2', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.36  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.36  tff(c_14, plain, (![A_7, B_14, C_15]: (v3_pre_topc('#skF_1'(A_7, B_14, C_15), A_7) | r2_waybel_7(A_7, B_14, C_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.36  tff(c_16, plain, (![A_7, B_14, C_15]: (m1_subset_1('#skF_1'(A_7, B_14, C_15), k1_zfmisc_1(u1_struct_0(A_7))) | r2_waybel_7(A_7, B_14, C_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.36  tff(c_12, plain, (![C_15, A_7, B_14]: (r2_hidden(C_15, '#skF_1'(A_7, B_14, C_15)) | r2_waybel_7(A_7, B_14, C_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.36  tff(c_58, plain, (![D_48, B_49, C_50, A_51]: (r2_hidden(D_48, B_49) | ~r2_hidden(C_50, D_48) | ~v3_pre_topc(D_48, A_51) | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0(A_51))) | ~r2_waybel_7(A_51, B_49, C_50) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.36  tff(c_105, plain, (![B_83, B_85, C_87, A_84, A_86]: (r2_hidden('#skF_1'(A_86, B_83, C_87), B_85) | ~v3_pre_topc('#skF_1'(A_86, B_83, C_87), A_84) | ~m1_subset_1('#skF_1'(A_86, B_83, C_87), k1_zfmisc_1(u1_struct_0(A_84))) | ~r2_waybel_7(A_84, B_85, C_87) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | r2_waybel_7(A_86, B_83, C_87) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86))), inference(resolution, [status(thm)], [c_12, c_58])).
% 2.27/1.36  tff(c_113, plain, (![A_88, B_89, C_90, B_91]: (r2_hidden('#skF_1'(A_88, B_89, C_90), B_91) | ~v3_pre_topc('#skF_1'(A_88, B_89, C_90), A_88) | ~r2_waybel_7(A_88, B_91, C_90) | r2_waybel_7(A_88, B_89, C_90) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(resolution, [status(thm)], [c_16, c_105])).
% 2.27/1.36  tff(c_117, plain, (![A_92, B_93, C_94, B_95]: (r2_hidden('#skF_1'(A_92, B_93, C_94), B_95) | ~r2_waybel_7(A_92, B_95, C_94) | r2_waybel_7(A_92, B_93, C_94) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(resolution, [status(thm)], [c_14, c_113])).
% 2.27/1.36  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.36  tff(c_129, plain, (![A_98, C_96, A_99, B_97, B_100]: (r2_hidden('#skF_1'(A_98, B_100, C_96), A_99) | ~m1_subset_1(B_97, k1_zfmisc_1(A_99)) | ~r2_waybel_7(A_98, B_97, C_96) | r2_waybel_7(A_98, B_100, C_96) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98))), inference(resolution, [status(thm)], [c_117, c_2])).
% 2.27/1.36  tff(c_136, plain, (![C_104, A_105, B_102, B_101, A_103]: (r2_hidden('#skF_1'(A_103, B_101, C_104), B_102) | ~r2_waybel_7(A_103, A_105, C_104) | r2_waybel_7(A_103, B_101, C_104) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | ~r1_tarski(A_105, B_102))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.27/1.36  tff(c_142, plain, (![B_101, B_102]: (r2_hidden('#skF_1'('#skF_2', B_101, '#skF_5'), B_102) | r2_waybel_7('#skF_2', B_101, '#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_3', B_102))), inference(resolution, [status(thm)], [c_20, c_136])).
% 2.27/1.36  tff(c_148, plain, (![B_106, B_107]: (r2_hidden('#skF_1'('#skF_2', B_106, '#skF_5'), B_107) | r2_waybel_7('#skF_2', B_106, '#skF_5') | ~r1_tarski('#skF_3', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_142])).
% 2.27/1.36  tff(c_10, plain, (![A_7, B_14, C_15]: (~r2_hidden('#skF_1'(A_7, B_14, C_15), B_14) | r2_waybel_7(A_7, B_14, C_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.36  tff(c_154, plain, (![B_107]: (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | r2_waybel_7('#skF_2', B_107, '#skF_5') | ~r1_tarski('#skF_3', B_107))), inference(resolution, [status(thm)], [c_148, c_10])).
% 2.27/1.36  tff(c_162, plain, (![B_108]: (r2_waybel_7('#skF_2', B_108, '#skF_5') | ~r1_tarski('#skF_3', B_108))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_154])).
% 2.27/1.36  tff(c_18, plain, (~r2_waybel_7('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.36  tff(c_169, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_162, c_18])).
% 2.27/1.36  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_169])).
% 2.27/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.36  
% 2.27/1.36  Inference rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Ref     : 0
% 2.27/1.36  #Sup     : 32
% 2.27/1.36  #Fact    : 0
% 2.27/1.36  #Define  : 0
% 2.27/1.36  #Split   : 0
% 2.27/1.36  #Chain   : 0
% 2.27/1.36  #Close   : 0
% 2.27/1.36  
% 2.27/1.36  Ordering : KBO
% 2.27/1.36  
% 2.27/1.36  Simplification rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Subsume      : 5
% 2.27/1.36  #Demod        : 11
% 2.27/1.36  #Tautology    : 2
% 2.27/1.36  #SimpNegUnit  : 0
% 2.27/1.36  #BackRed      : 0
% 2.27/1.36  
% 2.27/1.36  #Partial instantiations: 0
% 2.27/1.36  #Strategies tried      : 1
% 2.27/1.36  
% 2.27/1.36  Timing (in seconds)
% 2.27/1.36  ----------------------
% 2.27/1.36  Preprocessing        : 0.27
% 2.27/1.36  Parsing              : 0.15
% 2.27/1.36  CNF conversion       : 0.02
% 2.27/1.36  Main loop            : 0.28
% 2.27/1.36  Inferencing          : 0.12
% 2.27/1.36  Reduction            : 0.06
% 2.27/1.36  Demodulation         : 0.05
% 2.27/1.36  BG Simplification    : 0.01
% 2.27/1.36  Subsumption          : 0.06
% 2.27/1.36  Abstraction          : 0.01
% 2.27/1.36  MUC search           : 0.00
% 2.27/1.36  Cooper               : 0.00
% 2.27/1.36  Total                : 0.59
% 2.27/1.36  Index Insertion      : 0.00
% 2.27/1.36  Index Deletion       : 0.00
% 2.27/1.36  Index Matching       : 0.00
% 2.27/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
