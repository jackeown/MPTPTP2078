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
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 150 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  130 ( 320 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_64,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    m1_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_87,plain,(
    ! [B_69,A_70] :
      ( l1_pre_topc(B_69)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_87])).

tff(c_93,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_90])).

tff(c_44,plain,(
    ! [B_36,A_14] :
      ( r1_tarski(k2_struct_0(B_36),k2_struct_0(A_14))
      | ~ m1_pre_topc(B_36,A_14)
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77,B_78),A_77)
      | r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [A_77] : r1_tarski(A_77,A_77) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_133,plain,(
    ! [A_6,B_78] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_6),B_78),A_6)
      | r1_tarski(k1_zfmisc_1(A_6),B_78) ) ),
    inference(resolution,[status(thm)],[c_123,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [A_106,B_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(A_106,B_107),B_108)
      | ~ r1_tarski(B_109,B_108)
      | ~ r1_tarski(A_106,B_109)
      | r1_tarski(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_1283,plain,(
    ! [A_219,B_220,A_221,B_222] :
      ( r2_hidden('#skF_1'(A_219,B_220),A_221)
      | ~ r1_tarski(A_219,'#skF_1'(k1_zfmisc_1(A_221),B_222))
      | r1_tarski(A_219,B_220)
      | r1_tarski(k1_zfmisc_1(A_221),B_222) ) ),
    inference(resolution,[status(thm)],[c_133,c_200])).

tff(c_1341,plain,(
    ! [A_226,B_227,B_228] :
      ( r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_226),B_227),B_228),A_226)
      | r1_tarski('#skF_1'(k1_zfmisc_1(A_226),B_227),B_228)
      | r1_tarski(k1_zfmisc_1(A_226),B_227) ) ),
    inference(resolution,[status(thm)],[c_132,c_1283])).

tff(c_4268,plain,(
    ! [A_425,B_426,B_427,B_428] :
      ( r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_425),B_426),B_427),B_428)
      | ~ r1_tarski(A_425,B_428)
      | r1_tarski('#skF_1'(k1_zfmisc_1(A_425),B_426),B_427)
      | r1_tarski(k1_zfmisc_1(A_425),B_426) ) ),
    inference(resolution,[status(thm)],[c_1341,c_2])).

tff(c_4286,plain,(
    ! [A_429,B_430,B_431] :
      ( ~ r1_tarski(A_429,B_430)
      | r1_tarski('#skF_1'(k1_zfmisc_1(A_429),B_431),B_430)
      | r1_tarski(k1_zfmisc_1(A_429),B_431) ) ),
    inference(resolution,[status(thm)],[c_4268,c_4])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_75,B_76] :
      ( ~ r2_hidden('#skF_1'(A_75,B_76),B_76)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_75,A_6] :
      ( r1_tarski(A_75,k1_zfmisc_1(A_6))
      | ~ r1_tarski('#skF_1'(A_75,k1_zfmisc_1(A_6)),A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_4364,plain,(
    ! [A_429,B_430] :
      ( ~ r1_tarski(A_429,B_430)
      | r1_tarski(k1_zfmisc_1(A_429),k1_zfmisc_1(B_430)) ) ),
    inference(resolution,[status(thm)],[c_4286,c_122])).

tff(c_54,plain,(
    ! [A_54] :
      ( l1_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_97,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_93,c_70])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_98,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60])).

tff(c_108,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    r1_tarski('#skF_9',k1_zfmisc_1(k2_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_98,c_108])).

tff(c_4376,plain,(
    ! [A_435,B_436] :
      ( ~ r1_tarski(A_435,B_436)
      | r1_tarski(k1_zfmisc_1(A_435),k1_zfmisc_1(B_436)) ) ),
    inference(resolution,[status(thm)],[c_4286,c_122])).

tff(c_141,plain,(
    ! [C_10,B_81,A_6] :
      ( r2_hidden(C_10,B_81)
      | ~ r1_tarski(k1_zfmisc_1(A_6),B_81)
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_4640,plain,(
    ! [C_442,B_443,A_444] :
      ( r2_hidden(C_442,k1_zfmisc_1(B_443))
      | ~ r1_tarski(C_442,A_444)
      | ~ r1_tarski(A_444,B_443) ) ),
    inference(resolution,[status(thm)],[c_4376,c_141])).

tff(c_4797,plain,(
    ! [B_445] :
      ( r2_hidden('#skF_9',k1_zfmisc_1(B_445))
      | ~ r1_tarski(k1_zfmisc_1(k2_struct_0('#skF_8')),B_445) ) ),
    inference(resolution,[status(thm)],[c_115,c_4640])).

tff(c_4846,plain,(
    ! [B_446] :
      ( r2_hidden('#skF_9',k1_zfmisc_1(k1_zfmisc_1(B_446)))
      | ~ r1_tarski(k2_struct_0('#skF_8'),B_446) ) ),
    inference(resolution,[status(thm)],[c_4364,c_4797])).

tff(c_4854,plain,(
    ! [B_447] :
      ( r1_tarski('#skF_9',k1_zfmisc_1(B_447))
      | ~ r1_tarski(k2_struct_0('#skF_8'),B_447) ) ),
    inference(resolution,[status(thm)],[c_4846,c_8])).

tff(c_4878,plain,(
    ! [A_14] :
      ( r1_tarski('#skF_9',k1_zfmisc_1(k2_struct_0(A_14)))
      | ~ m1_pre_topc('#skF_8',A_14)
      | ~ l1_pre_topc('#skF_8')
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_44,c_4854])).

tff(c_4937,plain,(
    ! [A_449] :
      ( r1_tarski('#skF_9',k1_zfmisc_1(k2_struct_0(A_449)))
      | ~ m1_pre_topc('#skF_8',A_449)
      | ~ l1_pre_topc(A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_4878])).

tff(c_81,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(A_65,k1_zfmisc_1(B_66))
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_71])).

tff(c_58,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_76,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_9',k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_81,c_76])).

tff(c_4962,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_4937,c_85])).

tff(c_4978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:22:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.73  
% 7.84/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.73  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 7.84/2.73  
% 7.84/2.73  %Foreground sorts:
% 7.84/2.73  
% 7.84/2.73  
% 7.84/2.73  %Background operators:
% 7.84/2.73  
% 7.84/2.73  
% 7.84/2.73  %Foreground operators:
% 7.84/2.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.84/2.73  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.84/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.84/2.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.84/2.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.84/2.73  tff('#skF_7', type, '#skF_7': $i).
% 7.84/2.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.84/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.84/2.73  tff('#skF_9', type, '#skF_9': $i).
% 7.84/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.84/2.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.84/2.73  tff('#skF_8', type, '#skF_8': $i).
% 7.84/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.84/2.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.84/2.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.84/2.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.84/2.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.84/2.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.84/2.73  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.84/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.84/2.73  
% 7.84/2.74  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 7.84/2.74  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.84/2.74  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 7.84/2.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.84/2.74  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.84/2.74  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.84/2.74  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.84/2.74  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.84/2.74  tff(c_64, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.84/2.74  tff(c_62, plain, (m1_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.84/2.74  tff(c_87, plain, (![B_69, A_70]: (l1_pre_topc(B_69) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.84/2.74  tff(c_90, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_62, c_87])).
% 7.84/2.74  tff(c_93, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_90])).
% 7.84/2.74  tff(c_44, plain, (![B_36, A_14]: (r1_tarski(k2_struct_0(B_36), k2_struct_0(A_14)) | ~m1_pre_topc(B_36, A_14) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.84/2.74  tff(c_123, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77, B_78), A_77) | r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.84/2.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.84/2.74  tff(c_132, plain, (![A_77]: (r1_tarski(A_77, A_77))), inference(resolution, [status(thm)], [c_123, c_4])).
% 7.84/2.74  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.84/2.74  tff(c_133, plain, (![A_6, B_78]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_6), B_78), A_6) | r1_tarski(k1_zfmisc_1(A_6), B_78))), inference(resolution, [status(thm)], [c_123, c_8])).
% 7.84/2.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.84/2.74  tff(c_135, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.84/2.74  tff(c_156, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_135])).
% 7.84/2.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.84/2.74  tff(c_200, plain, (![A_106, B_107, B_108, B_109]: (r2_hidden('#skF_1'(A_106, B_107), B_108) | ~r1_tarski(B_109, B_108) | ~r1_tarski(A_106, B_109) | r1_tarski(A_106, B_107))), inference(resolution, [status(thm)], [c_156, c_2])).
% 7.84/2.74  tff(c_1283, plain, (![A_219, B_220, A_221, B_222]: (r2_hidden('#skF_1'(A_219, B_220), A_221) | ~r1_tarski(A_219, '#skF_1'(k1_zfmisc_1(A_221), B_222)) | r1_tarski(A_219, B_220) | r1_tarski(k1_zfmisc_1(A_221), B_222))), inference(resolution, [status(thm)], [c_133, c_200])).
% 7.84/2.74  tff(c_1341, plain, (![A_226, B_227, B_228]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_226), B_227), B_228), A_226) | r1_tarski('#skF_1'(k1_zfmisc_1(A_226), B_227), B_228) | r1_tarski(k1_zfmisc_1(A_226), B_227))), inference(resolution, [status(thm)], [c_132, c_1283])).
% 7.84/2.74  tff(c_4268, plain, (![A_425, B_426, B_427, B_428]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_425), B_426), B_427), B_428) | ~r1_tarski(A_425, B_428) | r1_tarski('#skF_1'(k1_zfmisc_1(A_425), B_426), B_427) | r1_tarski(k1_zfmisc_1(A_425), B_426))), inference(resolution, [status(thm)], [c_1341, c_2])).
% 7.84/2.74  tff(c_4286, plain, (![A_429, B_430, B_431]: (~r1_tarski(A_429, B_430) | r1_tarski('#skF_1'(k1_zfmisc_1(A_429), B_431), B_430) | r1_tarski(k1_zfmisc_1(A_429), B_431))), inference(resolution, [status(thm)], [c_4268, c_4])).
% 7.84/2.74  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.84/2.74  tff(c_117, plain, (![A_75, B_76]: (~r2_hidden('#skF_1'(A_75, B_76), B_76) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.84/2.74  tff(c_122, plain, (![A_75, A_6]: (r1_tarski(A_75, k1_zfmisc_1(A_6)) | ~r1_tarski('#skF_1'(A_75, k1_zfmisc_1(A_6)), A_6))), inference(resolution, [status(thm)], [c_10, c_117])).
% 7.84/2.74  tff(c_4364, plain, (![A_429, B_430]: (~r1_tarski(A_429, B_430) | r1_tarski(k1_zfmisc_1(A_429), k1_zfmisc_1(B_430)))), inference(resolution, [status(thm)], [c_4286, c_122])).
% 7.84/2.74  tff(c_54, plain, (![A_54]: (l1_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.84/2.74  tff(c_66, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.84/2.74  tff(c_70, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_54, c_66])).
% 7.84/2.74  tff(c_97, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_93, c_70])).
% 7.84/2.74  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.84/2.74  tff(c_98, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60])).
% 7.84/2.74  tff(c_108, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~m1_subset_1(A_73, k1_zfmisc_1(B_74)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.84/2.74  tff(c_115, plain, (r1_tarski('#skF_9', k1_zfmisc_1(k2_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_98, c_108])).
% 7.84/2.74  tff(c_4376, plain, (![A_435, B_436]: (~r1_tarski(A_435, B_436) | r1_tarski(k1_zfmisc_1(A_435), k1_zfmisc_1(B_436)))), inference(resolution, [status(thm)], [c_4286, c_122])).
% 7.84/2.74  tff(c_141, plain, (![C_10, B_81, A_6]: (r2_hidden(C_10, B_81) | ~r1_tarski(k1_zfmisc_1(A_6), B_81) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_10, c_135])).
% 7.84/2.74  tff(c_4640, plain, (![C_442, B_443, A_444]: (r2_hidden(C_442, k1_zfmisc_1(B_443)) | ~r1_tarski(C_442, A_444) | ~r1_tarski(A_444, B_443))), inference(resolution, [status(thm)], [c_4376, c_141])).
% 7.84/2.74  tff(c_4797, plain, (![B_445]: (r2_hidden('#skF_9', k1_zfmisc_1(B_445)) | ~r1_tarski(k1_zfmisc_1(k2_struct_0('#skF_8')), B_445))), inference(resolution, [status(thm)], [c_115, c_4640])).
% 7.84/2.74  tff(c_4846, plain, (![B_446]: (r2_hidden('#skF_9', k1_zfmisc_1(k1_zfmisc_1(B_446))) | ~r1_tarski(k2_struct_0('#skF_8'), B_446))), inference(resolution, [status(thm)], [c_4364, c_4797])).
% 7.84/2.74  tff(c_4854, plain, (![B_447]: (r1_tarski('#skF_9', k1_zfmisc_1(B_447)) | ~r1_tarski(k2_struct_0('#skF_8'), B_447))), inference(resolution, [status(thm)], [c_4846, c_8])).
% 7.84/2.74  tff(c_4878, plain, (![A_14]: (r1_tarski('#skF_9', k1_zfmisc_1(k2_struct_0(A_14))) | ~m1_pre_topc('#skF_8', A_14) | ~l1_pre_topc('#skF_8') | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_44, c_4854])).
% 7.84/2.74  tff(c_4937, plain, (![A_449]: (r1_tarski('#skF_9', k1_zfmisc_1(k2_struct_0(A_449))) | ~m1_pre_topc('#skF_8', A_449) | ~l1_pre_topc(A_449))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_4878])).
% 7.84/2.74  tff(c_81, plain, (![A_65, B_66]: (m1_subset_1(A_65, k1_zfmisc_1(B_66)) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.84/2.74  tff(c_71, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_54, c_66])).
% 7.84/2.74  tff(c_75, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_64, c_71])).
% 7.84/2.74  tff(c_58, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.84/2.74  tff(c_76, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58])).
% 7.84/2.74  tff(c_85, plain, (~r1_tarski('#skF_9', k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_81, c_76])).
% 7.84/2.74  tff(c_4962, plain, (~m1_pre_topc('#skF_8', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_4937, c_85])).
% 7.84/2.74  tff(c_4978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_4962])).
% 7.84/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.74  
% 7.84/2.74  Inference rules
% 7.84/2.74  ----------------------
% 7.84/2.74  #Ref     : 0
% 7.84/2.74  #Sup     : 1300
% 7.84/2.74  #Fact    : 0
% 7.84/2.74  #Define  : 0
% 7.84/2.74  #Split   : 20
% 7.84/2.74  #Chain   : 0
% 7.84/2.74  #Close   : 0
% 7.84/2.74  
% 7.84/2.74  Ordering : KBO
% 7.84/2.74  
% 7.84/2.74  Simplification rules
% 7.84/2.74  ----------------------
% 7.84/2.74  #Subsume      : 283
% 7.84/2.74  #Demod        : 129
% 7.84/2.74  #Tautology    : 59
% 7.84/2.74  #SimpNegUnit  : 0
% 7.84/2.74  #BackRed      : 2
% 7.84/2.74  
% 7.84/2.74  #Partial instantiations: 0
% 7.84/2.74  #Strategies tried      : 1
% 7.84/2.74  
% 7.84/2.74  Timing (in seconds)
% 7.84/2.74  ----------------------
% 7.84/2.75  Preprocessing        : 0.33
% 7.84/2.75  Parsing              : 0.16
% 7.84/2.75  CNF conversion       : 0.03
% 7.84/2.75  Main loop            : 1.56
% 7.84/2.75  Inferencing          : 0.44
% 7.84/2.75  Reduction            : 0.37
% 7.84/2.75  Demodulation         : 0.23
% 7.84/2.75  BG Simplification    : 0.05
% 7.84/2.75  Subsumption          : 0.59
% 7.84/2.75  Abstraction          : 0.07
% 8.11/2.75  MUC search           : 0.00
% 8.11/2.75  Cooper               : 0.00
% 8.11/2.75  Total                : 1.92
% 8.11/2.75  Index Insertion      : 0.00
% 8.11/2.75  Index Deletion       : 0.00
% 8.11/2.75  Index Matching       : 0.00
% 8.11/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
