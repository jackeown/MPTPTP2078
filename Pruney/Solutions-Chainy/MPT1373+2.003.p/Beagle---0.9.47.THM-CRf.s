%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:01 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 898 expanded)
%              Number of leaves         :   33 ( 318 expanded)
%              Depth                    :   19
%              Number of atoms          :  268 (2522 expanded)
%              Number of equality atoms :   31 ( 349 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( v2_compts_1(C,A)
                      <=> v2_compts_1(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_50,axiom,(
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

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2692,plain,(
    ! [B_267,A_268] :
      ( l1_pre_topc(B_267)
      | ~ m1_pre_topc(B_267,A_268)
      | ~ l1_pre_topc(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2695,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2692])).

tff(c_2698,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2695])).

tff(c_36,plain,(
    ! [A_44] :
      ( l1_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_85] :
      ( u1_struct_0(A_85) = k2_struct_0(A_85)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_2702,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2698,c_79])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2703,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_52])).

tff(c_2730,plain,(
    ! [A_275,B_276] :
      ( m1_pre_topc(k1_pre_topc(A_275,B_276),A_275)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2732,plain,(
    ! [B_276] :
      ( m1_pre_topc(k1_pre_topc('#skF_6',B_276),'#skF_6')
      | ~ m1_subset_1(B_276,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2702,c_2730])).

tff(c_2739,plain,(
    ! [B_277] :
      ( m1_pre_topc(k1_pre_topc('#skF_6',B_277),'#skF_6')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_2732])).

tff(c_2743,plain,(
    m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2703,c_2739])).

tff(c_38,plain,(
    ! [B_47,A_45] :
      ( l1_pre_topc(B_47)
      | ~ m1_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2746,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_2743,c_38])).

tff(c_2749,plain,(
    l1_pre_topc(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_2746])).

tff(c_2754,plain,(
    ! [A_278,B_279] :
      ( u1_struct_0(k1_pre_topc(A_278,B_279)) = B_279
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2757,plain,(
    ! [B_279] :
      ( u1_struct_0(k1_pre_topc('#skF_6',B_279)) = B_279
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2702,c_2754])).

tff(c_2836,plain,(
    ! [B_282] :
      ( u1_struct_0(k1_pre_topc('#skF_6',B_282)) = B_282
      | ~ m1_subset_1(B_282,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_2757])).

tff(c_2840,plain,(
    u1_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2703,c_2836])).

tff(c_2753,plain,(
    u1_struct_0(k1_pre_topc('#skF_6','#skF_8')) = k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_2749,c_79])).

tff(c_2841,plain,(
    k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2840,c_2753])).

tff(c_22,plain,(
    ! [B_24,A_2] :
      ( r1_tarski(k2_struct_0(B_24),k2_struct_0(A_2))
      | ~ m1_pre_topc(B_24,A_2)
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2895,plain,(
    ! [A_2] :
      ( r1_tarski('#skF_8',k2_struct_0(A_2))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_2)
      | ~ l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2841,c_22])).

tff(c_2902,plain,(
    ! [A_2] :
      ( r1_tarski('#skF_8',k2_struct_0(A_2))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_2895])).

tff(c_50,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_66,plain,
    ( v2_compts_1('#skF_7','#skF_5')
    | v2_compts_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_69,plain,
    ( v2_compts_1('#skF_8','#skF_5')
    | v2_compts_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_66])).

tff(c_80,plain,(
    v2_compts_1('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_60,plain,
    ( ~ v2_compts_1('#skF_8','#skF_6')
    | ~ v2_compts_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_67,plain,
    ( ~ v2_compts_1('#skF_8','#skF_6')
    | ~ v2_compts_1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60])).

tff(c_82,plain,(
    ~ v2_compts_1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_67])).

tff(c_83,plain,(
    ! [A_86] :
      ( u1_struct_0(A_86) = k2_struct_0(A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_87,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54])).

tff(c_88,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_68])).

tff(c_93,plain,(
    ! [B_87,A_88] :
      ( l1_pre_topc(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_96,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_93])).

tff(c_99,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_96])).

tff(c_103,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_99,c_79])).

tff(c_116,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_52])).

tff(c_179,plain,(
    ! [A_99,B_100] :
      ( m1_pre_topc(k1_pre_topc(A_99,B_100),A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_185,plain,(
    ! [B_100] :
      ( m1_pre_topc(k1_pre_topc('#skF_6',B_100),'#skF_6')
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_179])).

tff(c_222,plain,(
    ! [B_102] :
      ( m1_pre_topc(k1_pre_topc('#skF_6',B_102),'#skF_6')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_185])).

tff(c_226,plain,(
    m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_116,c_222])).

tff(c_229,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_226,c_38])).

tff(c_232,plain,(
    l1_pre_topc(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_229])).

tff(c_137,plain,(
    ! [A_93,B_94] :
      ( u1_struct_0(k1_pre_topc(A_93,B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_140,plain,(
    ! [B_94] :
      ( u1_struct_0(k1_pre_topc('#skF_6',B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_137])).

tff(c_148,plain,(
    ! [B_95] :
      ( u1_struct_0(k1_pre_topc('#skF_6',B_95)) = B_95
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_140])).

tff(c_152,plain,(
    u1_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_116,c_148])).

tff(c_265,plain,(
    u1_struct_0(k1_pre_topc('#skF_6','#skF_8')) = k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_232,c_79])).

tff(c_267,plain,(
    k2_struct_0(k1_pre_topc('#skF_6','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_265])).

tff(c_271,plain,(
    ! [A_2] :
      ( r1_tarski('#skF_8',k2_struct_0(A_2))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_2)
      | ~ l1_pre_topc(k1_pre_topc('#skF_6','#skF_8'))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_22])).

tff(c_278,plain,(
    ! [A_2] :
      ( r1_tarski('#skF_8',k2_struct_0(A_2))
      | ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_271])).

tff(c_965,plain,(
    ! [A_162,B_163,C_164] :
      ( m1_subset_1('#skF_4'(A_162,B_163,C_164),k1_zfmisc_1(u1_struct_0(B_163)))
      | v2_compts_1(C_164,A_162)
      | ~ r1_tarski(C_164,k2_struct_0(B_163))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ m1_pre_topc(B_163,A_162)
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2479,plain,(
    ! [A_260,C_261] :
      ( m1_subset_1('#skF_4'(A_260,'#skF_6',C_261),k1_zfmisc_1(k2_struct_0('#skF_6')))
      | v2_compts_1(C_261,A_260)
      | ~ r1_tarski(C_261,k2_struct_0('#skF_6'))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ m1_pre_topc('#skF_6',A_260)
      | ~ l1_pre_topc(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_965])).

tff(c_34,plain,(
    ! [A_42,B_43] :
      ( v1_pre_topc(k1_pre_topc(A_42,B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_120,plain,(
    ! [B_43] :
      ( v1_pre_topc(k1_pre_topc('#skF_6',B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_34])).

tff(c_124,plain,(
    ! [B_43] :
      ( v1_pre_topc(k1_pre_topc('#skF_6',B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_120])).

tff(c_2506,plain,(
    ! [A_262,C_263] :
      ( v1_pre_topc(k1_pre_topc('#skF_6','#skF_4'(A_262,'#skF_6',C_263)))
      | v2_compts_1(C_263,A_262)
      | ~ r1_tarski(C_263,k2_struct_0('#skF_6'))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ m1_pre_topc('#skF_6',A_262)
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_2479,c_124])).

tff(c_2554,plain,(
    ! [C_263] :
      ( v1_pre_topc(k1_pre_topc('#skF_6','#skF_4'('#skF_5','#skF_6',C_263)))
      | v2_compts_1(C_263,'#skF_5')
      | ~ r1_tarski(C_263,k2_struct_0('#skF_6'))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_6','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2506])).

tff(c_2567,plain,(
    ! [C_264] :
      ( v1_pre_topc(k1_pre_topc('#skF_6','#skF_4'('#skF_5','#skF_6',C_264)))
      | v2_compts_1(C_264,'#skF_5')
      | ~ r1_tarski(C_264,k2_struct_0('#skF_6'))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2554])).

tff(c_2582,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_6','#skF_4'('#skF_5','#skF_6','#skF_8')))
    | v2_compts_1('#skF_8','#skF_5')
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_88,c_2567])).

tff(c_2589,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_6','#skF_4'('#skF_5','#skF_6','#skF_8')))
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2582])).

tff(c_2590,plain,(
    ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2589])).

tff(c_2596,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_278,c_2590])).

tff(c_2603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_226,c_2596])).

tff(c_2605,plain,(
    r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2589])).

tff(c_46,plain,(
    ! [A_51,B_63,C_69] :
      ( '#skF_4'(A_51,B_63,C_69) = C_69
      | v2_compts_1(C_69,A_51)
      | ~ r1_tarski(C_69,k2_struct_0(B_63))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_63,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2609,plain,(
    ! [A_265] :
      ( '#skF_4'(A_265,'#skF_6','#skF_8') = '#skF_8'
      | v2_compts_1('#skF_8',A_265)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ m1_pre_topc('#skF_6',A_265)
      | ~ l1_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_2605,c_46])).

tff(c_2645,plain,
    ( '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8'
    | v2_compts_1('#skF_8','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2609])).

tff(c_2653,plain,
    ( '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8'
    | v2_compts_1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_88,c_2645])).

tff(c_2654,plain,(
    '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2653])).

tff(c_44,plain,(
    ! [A_51,B_63,C_69] :
      ( ~ v2_compts_1('#skF_4'(A_51,B_63,C_69),B_63)
      | v2_compts_1(C_69,A_51)
      | ~ r1_tarski(C_69,k2_struct_0(B_63))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_63,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2665,plain,
    ( ~ v2_compts_1('#skF_8','#skF_6')
    | v2_compts_1('#skF_8','#skF_5')
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2654,c_44])).

tff(c_2675,plain,(
    v2_compts_1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_88,c_87,c_2605,c_80,c_2665])).

tff(c_2677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2675])).

tff(c_2679,plain,(
    ~ v2_compts_1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_2678,plain,(
    v2_compts_1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_2682,plain,(
    ! [A_266] :
      ( u1_struct_0(A_266) = k2_struct_0(A_266)
      | ~ l1_pre_topc(A_266) ) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_2686,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2682])).

tff(c_2687,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2686,c_68])).

tff(c_3541,plain,(
    ! [D_341,B_342,A_343] :
      ( v2_compts_1(D_341,B_342)
      | ~ m1_subset_1(D_341,k1_zfmisc_1(u1_struct_0(B_342)))
      | ~ v2_compts_1(D_341,A_343)
      | ~ r1_tarski(D_341,k2_struct_0(B_342))
      | ~ m1_subset_1(D_341,k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_pre_topc(B_342,A_343)
      | ~ l1_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5110,plain,(
    ! [D_441,A_442] :
      ( v2_compts_1(D_441,'#skF_6')
      | ~ m1_subset_1(D_441,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ v2_compts_1(D_441,A_442)
      | ~ r1_tarski(D_441,k2_struct_0('#skF_6'))
      | ~ m1_subset_1(D_441,k1_zfmisc_1(u1_struct_0(A_442)))
      | ~ m1_pre_topc('#skF_6',A_442)
      | ~ l1_pre_topc(A_442) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2702,c_3541])).

tff(c_5158,plain,(
    ! [D_441] :
      ( v2_compts_1(D_441,'#skF_6')
      | ~ m1_subset_1(D_441,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ v2_compts_1(D_441,'#skF_5')
      | ~ r1_tarski(D_441,k2_struct_0('#skF_6'))
      | ~ m1_subset_1(D_441,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_6','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2686,c_5110])).

tff(c_5171,plain,(
    ! [D_443] :
      ( v2_compts_1(D_443,'#skF_6')
      | ~ m1_subset_1(D_443,k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ v2_compts_1(D_443,'#skF_5')
      | ~ r1_tarski(D_443,k2_struct_0('#skF_6'))
      | ~ m1_subset_1(D_443,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_5158])).

tff(c_5186,plain,
    ( v2_compts_1('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_6')))
    | ~ v2_compts_1('#skF_8','#skF_5')
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2687,c_5171])).

tff(c_5193,plain,
    ( v2_compts_1('#skF_8','#skF_6')
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2678,c_2703,c_5186])).

tff(c_5194,plain,(
    ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2679,c_5193])).

tff(c_5197,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_6','#skF_8'),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_2902,c_5194])).

tff(c_5204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_2743,c_5197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.44/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.56  
% 7.44/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.56  %$ v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 7.44/2.56  
% 7.44/2.56  %Foreground sorts:
% 7.44/2.56  
% 7.44/2.56  
% 7.44/2.56  %Background operators:
% 7.44/2.56  
% 7.44/2.56  
% 7.44/2.56  %Foreground operators:
% 7.44/2.56  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 7.44/2.56  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 7.44/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.44/2.56  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.44/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.44/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.44/2.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.44/2.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.44/2.56  tff('#skF_7', type, '#skF_7': $i).
% 7.44/2.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.44/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.44/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.44/2.56  tff('#skF_6', type, '#skF_6': $i).
% 7.44/2.56  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.44/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.44/2.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.44/2.56  tff('#skF_8', type, '#skF_8': $i).
% 7.44/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.44/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.44/2.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.44/2.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.44/2.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.44/2.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.44/2.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.44/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.44/2.56  
% 7.44/2.58  tff(f_113, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((C = D) => (v2_compts_1(C, A) <=> v2_compts_1(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_compts_1)).
% 7.44/2.58  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.44/2.58  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.44/2.58  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.44/2.58  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 7.44/2.58  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 7.44/2.58  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 7.44/2.58  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 7.44/2.58  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.44/2.58  tff(c_56, plain, (m1_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.44/2.58  tff(c_2692, plain, (![B_267, A_268]: (l1_pre_topc(B_267) | ~m1_pre_topc(B_267, A_268) | ~l1_pre_topc(A_268))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.44/2.58  tff(c_2695, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2692])).
% 7.44/2.58  tff(c_2698, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2695])).
% 7.44/2.58  tff(c_36, plain, (![A_44]: (l1_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.44/2.58  tff(c_75, plain, (![A_85]: (u1_struct_0(A_85)=k2_struct_0(A_85) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.44/2.58  tff(c_79, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_36, c_75])).
% 7.44/2.58  tff(c_2702, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_2698, c_79])).
% 7.44/2.58  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.44/2.58  tff(c_2703, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2702, c_52])).
% 7.44/2.58  tff(c_2730, plain, (![A_275, B_276]: (m1_pre_topc(k1_pre_topc(A_275, B_276), A_275) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.44/2.58  tff(c_2732, plain, (![B_276]: (m1_pre_topc(k1_pre_topc('#skF_6', B_276), '#skF_6') | ~m1_subset_1(B_276, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2702, c_2730])).
% 7.44/2.58  tff(c_2739, plain, (![B_277]: (m1_pre_topc(k1_pre_topc('#skF_6', B_277), '#skF_6') | ~m1_subset_1(B_277, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_2698, c_2732])).
% 7.44/2.58  tff(c_2743, plain, (m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_2703, c_2739])).
% 7.44/2.58  tff(c_38, plain, (![B_47, A_45]: (l1_pre_topc(B_47) | ~m1_pre_topc(B_47, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.44/2.58  tff(c_2746, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_2743, c_38])).
% 7.44/2.58  tff(c_2749, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2698, c_2746])).
% 7.44/2.58  tff(c_2754, plain, (![A_278, B_279]: (u1_struct_0(k1_pre_topc(A_278, B_279))=B_279 | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.44/2.58  tff(c_2757, plain, (![B_279]: (u1_struct_0(k1_pre_topc('#skF_6', B_279))=B_279 | ~m1_subset_1(B_279, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2702, c_2754])).
% 7.44/2.58  tff(c_2836, plain, (![B_282]: (u1_struct_0(k1_pre_topc('#skF_6', B_282))=B_282 | ~m1_subset_1(B_282, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_2698, c_2757])).
% 7.44/2.58  tff(c_2840, plain, (u1_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8'), inference(resolution, [status(thm)], [c_2703, c_2836])).
% 7.44/2.58  tff(c_2753, plain, (u1_struct_0(k1_pre_topc('#skF_6', '#skF_8'))=k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_2749, c_79])).
% 7.44/2.58  tff(c_2841, plain, (k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2840, c_2753])).
% 7.44/2.58  tff(c_22, plain, (![B_24, A_2]: (r1_tarski(k2_struct_0(B_24), k2_struct_0(A_2)) | ~m1_pre_topc(B_24, A_2) | ~l1_pre_topc(B_24) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.44/2.58  tff(c_2895, plain, (![A_2]: (r1_tarski('#skF_8', k2_struct_0(A_2)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_2) | ~l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_2841, c_22])).
% 7.44/2.58  tff(c_2902, plain, (![A_2]: (r1_tarski('#skF_8', k2_struct_0(A_2)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_2) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2749, c_2895])).
% 7.44/2.58  tff(c_50, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.44/2.58  tff(c_66, plain, (v2_compts_1('#skF_7', '#skF_5') | v2_compts_1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.44/2.58  tff(c_69, plain, (v2_compts_1('#skF_8', '#skF_5') | v2_compts_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_66])).
% 7.44/2.58  tff(c_80, plain, (v2_compts_1('#skF_8', '#skF_6')), inference(splitLeft, [status(thm)], [c_69])).
% 7.44/2.58  tff(c_60, plain, (~v2_compts_1('#skF_8', '#skF_6') | ~v2_compts_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.44/2.58  tff(c_67, plain, (~v2_compts_1('#skF_8', '#skF_6') | ~v2_compts_1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60])).
% 7.44/2.58  tff(c_82, plain, (~v2_compts_1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_67])).
% 7.44/2.58  tff(c_83, plain, (![A_86]: (u1_struct_0(A_86)=k2_struct_0(A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_36, c_75])).
% 7.44/2.58  tff(c_87, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_83])).
% 7.44/2.58  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.44/2.58  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54])).
% 7.44/2.58  tff(c_88, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_68])).
% 7.44/2.58  tff(c_93, plain, (![B_87, A_88]: (l1_pre_topc(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.44/2.58  tff(c_96, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_56, c_93])).
% 7.44/2.58  tff(c_99, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_96])).
% 7.44/2.58  tff(c_103, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_99, c_79])).
% 7.44/2.58  tff(c_116, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_52])).
% 7.44/2.58  tff(c_179, plain, (![A_99, B_100]: (m1_pre_topc(k1_pre_topc(A_99, B_100), A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.44/2.58  tff(c_185, plain, (![B_100]: (m1_pre_topc(k1_pre_topc('#skF_6', B_100), '#skF_6') | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_179])).
% 7.44/2.58  tff(c_222, plain, (![B_102]: (m1_pre_topc(k1_pre_topc('#skF_6', B_102), '#skF_6') | ~m1_subset_1(B_102, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_185])).
% 7.44/2.58  tff(c_226, plain, (m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_116, c_222])).
% 7.44/2.58  tff(c_229, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_226, c_38])).
% 7.44/2.58  tff(c_232, plain, (l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_229])).
% 7.44/2.58  tff(c_137, plain, (![A_93, B_94]: (u1_struct_0(k1_pre_topc(A_93, B_94))=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.44/2.58  tff(c_140, plain, (![B_94]: (u1_struct_0(k1_pre_topc('#skF_6', B_94))=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_137])).
% 7.44/2.58  tff(c_148, plain, (![B_95]: (u1_struct_0(k1_pre_topc('#skF_6', B_95))=B_95 | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_140])).
% 7.44/2.58  tff(c_152, plain, (u1_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8'), inference(resolution, [status(thm)], [c_116, c_148])).
% 7.44/2.58  tff(c_265, plain, (u1_struct_0(k1_pre_topc('#skF_6', '#skF_8'))=k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_232, c_79])).
% 7.44/2.58  tff(c_267, plain, (k2_struct_0(k1_pre_topc('#skF_6', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_265])).
% 7.44/2.58  tff(c_271, plain, (![A_2]: (r1_tarski('#skF_8', k2_struct_0(A_2)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_2) | ~l1_pre_topc(k1_pre_topc('#skF_6', '#skF_8')) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_267, c_22])).
% 7.44/2.58  tff(c_278, plain, (![A_2]: (r1_tarski('#skF_8', k2_struct_0(A_2)) | ~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), A_2) | ~l1_pre_topc(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_271])).
% 7.44/2.58  tff(c_965, plain, (![A_162, B_163, C_164]: (m1_subset_1('#skF_4'(A_162, B_163, C_164), k1_zfmisc_1(u1_struct_0(B_163))) | v2_compts_1(C_164, A_162) | ~r1_tarski(C_164, k2_struct_0(B_163)) | ~m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0(A_162))) | ~m1_pre_topc(B_163, A_162) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.44/2.58  tff(c_2479, plain, (![A_260, C_261]: (m1_subset_1('#skF_4'(A_260, '#skF_6', C_261), k1_zfmisc_1(k2_struct_0('#skF_6'))) | v2_compts_1(C_261, A_260) | ~r1_tarski(C_261, k2_struct_0('#skF_6')) | ~m1_subset_1(C_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~m1_pre_topc('#skF_6', A_260) | ~l1_pre_topc(A_260))), inference(superposition, [status(thm), theory('equality')], [c_103, c_965])).
% 7.44/2.58  tff(c_34, plain, (![A_42, B_43]: (v1_pre_topc(k1_pre_topc(A_42, B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.44/2.58  tff(c_120, plain, (![B_43]: (v1_pre_topc(k1_pre_topc('#skF_6', B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_34])).
% 7.44/2.58  tff(c_124, plain, (![B_43]: (v1_pre_topc(k1_pre_topc('#skF_6', B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_120])).
% 7.44/2.58  tff(c_2506, plain, (![A_262, C_263]: (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_4'(A_262, '#skF_6', C_263))) | v2_compts_1(C_263, A_262) | ~r1_tarski(C_263, k2_struct_0('#skF_6')) | ~m1_subset_1(C_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~m1_pre_topc('#skF_6', A_262) | ~l1_pre_topc(A_262))), inference(resolution, [status(thm)], [c_2479, c_124])).
% 7.44/2.58  tff(c_2554, plain, (![C_263]: (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_263))) | v2_compts_1(C_263, '#skF_5') | ~r1_tarski(C_263, k2_struct_0('#skF_6')) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2506])).
% 7.44/2.58  tff(c_2567, plain, (![C_264]: (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_4'('#skF_5', '#skF_6', C_264))) | v2_compts_1(C_264, '#skF_5') | ~r1_tarski(C_264, k2_struct_0('#skF_6')) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2554])).
% 7.44/2.58  tff(c_2582, plain, (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_4'('#skF_5', '#skF_6', '#skF_8'))) | v2_compts_1('#skF_8', '#skF_5') | ~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_88, c_2567])).
% 7.44/2.58  tff(c_2589, plain, (v1_pre_topc(k1_pre_topc('#skF_6', '#skF_4'('#skF_5', '#skF_6', '#skF_8'))) | ~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_2582])).
% 7.44/2.58  tff(c_2590, plain, (~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_2589])).
% 7.44/2.58  tff(c_2596, plain, (~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_278, c_2590])).
% 7.44/2.58  tff(c_2603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_226, c_2596])).
% 7.44/2.58  tff(c_2605, plain, (r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_2589])).
% 7.44/2.58  tff(c_46, plain, (![A_51, B_63, C_69]: ('#skF_4'(A_51, B_63, C_69)=C_69 | v2_compts_1(C_69, A_51) | ~r1_tarski(C_69, k2_struct_0(B_63)) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_63, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.44/2.58  tff(c_2609, plain, (![A_265]: ('#skF_4'(A_265, '#skF_6', '#skF_8')='#skF_8' | v2_compts_1('#skF_8', A_265) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_265))) | ~m1_pre_topc('#skF_6', A_265) | ~l1_pre_topc(A_265))), inference(resolution, [status(thm)], [c_2605, c_46])).
% 7.44/2.58  tff(c_2645, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8' | v2_compts_1('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_87, c_2609])).
% 7.44/2.58  tff(c_2653, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8' | v2_compts_1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_88, c_2645])).
% 7.44/2.58  tff(c_2654, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_82, c_2653])).
% 7.44/2.58  tff(c_44, plain, (![A_51, B_63, C_69]: (~v2_compts_1('#skF_4'(A_51, B_63, C_69), B_63) | v2_compts_1(C_69, A_51) | ~r1_tarski(C_69, k2_struct_0(B_63)) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_63, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.44/2.58  tff(c_2665, plain, (~v2_compts_1('#skF_8', '#skF_6') | v2_compts_1('#skF_8', '#skF_5') | ~r1_tarski('#skF_8', k2_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2654, c_44])).
% 7.44/2.58  tff(c_2675, plain, (v2_compts_1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_88, c_87, c_2605, c_80, c_2665])).
% 7.44/2.58  tff(c_2677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2675])).
% 7.44/2.58  tff(c_2679, plain, (~v2_compts_1('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 7.44/2.58  tff(c_2678, plain, (v2_compts_1('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_69])).
% 7.44/2.58  tff(c_2682, plain, (![A_266]: (u1_struct_0(A_266)=k2_struct_0(A_266) | ~l1_pre_topc(A_266))), inference(resolution, [status(thm)], [c_36, c_75])).
% 7.44/2.58  tff(c_2686, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2682])).
% 7.44/2.58  tff(c_2687, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2686, c_68])).
% 7.44/2.58  tff(c_3541, plain, (![D_341, B_342, A_343]: (v2_compts_1(D_341, B_342) | ~m1_subset_1(D_341, k1_zfmisc_1(u1_struct_0(B_342))) | ~v2_compts_1(D_341, A_343) | ~r1_tarski(D_341, k2_struct_0(B_342)) | ~m1_subset_1(D_341, k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_pre_topc(B_342, A_343) | ~l1_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.44/2.58  tff(c_5110, plain, (![D_441, A_442]: (v2_compts_1(D_441, '#skF_6') | ~m1_subset_1(D_441, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~v2_compts_1(D_441, A_442) | ~r1_tarski(D_441, k2_struct_0('#skF_6')) | ~m1_subset_1(D_441, k1_zfmisc_1(u1_struct_0(A_442))) | ~m1_pre_topc('#skF_6', A_442) | ~l1_pre_topc(A_442))), inference(superposition, [status(thm), theory('equality')], [c_2702, c_3541])).
% 7.44/2.58  tff(c_5158, plain, (![D_441]: (v2_compts_1(D_441, '#skF_6') | ~m1_subset_1(D_441, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~v2_compts_1(D_441, '#skF_5') | ~r1_tarski(D_441, k2_struct_0('#skF_6')) | ~m1_subset_1(D_441, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2686, c_5110])).
% 7.44/2.58  tff(c_5171, plain, (![D_443]: (v2_compts_1(D_443, '#skF_6') | ~m1_subset_1(D_443, k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~v2_compts_1(D_443, '#skF_5') | ~r1_tarski(D_443, k2_struct_0('#skF_6')) | ~m1_subset_1(D_443, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_5158])).
% 7.44/2.58  tff(c_5186, plain, (v2_compts_1('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~v2_compts_1('#skF_8', '#skF_5') | ~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2687, c_5171])).
% 7.44/2.58  tff(c_5193, plain, (v2_compts_1('#skF_8', '#skF_6') | ~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2678, c_2703, c_5186])).
% 7.44/2.58  tff(c_5194, plain, (~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_2679, c_5193])).
% 7.44/2.58  tff(c_5197, plain, (~m1_pre_topc(k1_pre_topc('#skF_6', '#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_2902, c_5194])).
% 7.44/2.58  tff(c_5204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2698, c_2743, c_5197])).
% 7.44/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.58  
% 7.44/2.58  Inference rules
% 7.44/2.58  ----------------------
% 7.44/2.58  #Ref     : 0
% 7.44/2.58  #Sup     : 1323
% 7.44/2.58  #Fact    : 0
% 7.44/2.58  #Define  : 0
% 7.44/2.58  #Split   : 28
% 7.44/2.58  #Chain   : 0
% 7.44/2.58  #Close   : 0
% 7.44/2.58  
% 7.44/2.58  Ordering : KBO
% 7.44/2.58  
% 7.44/2.58  Simplification rules
% 7.44/2.58  ----------------------
% 7.44/2.58  #Subsume      : 105
% 7.44/2.58  #Demod        : 554
% 7.44/2.58  #Tautology    : 137
% 7.44/2.58  #SimpNegUnit  : 58
% 7.44/2.58  #BackRed      : 6
% 7.44/2.58  
% 7.44/2.58  #Partial instantiations: 0
% 7.44/2.58  #Strategies tried      : 1
% 7.44/2.58  
% 7.44/2.58  Timing (in seconds)
% 7.44/2.58  ----------------------
% 7.44/2.58  Preprocessing        : 0.33
% 7.44/2.58  Parsing              : 0.16
% 7.44/2.58  CNF conversion       : 0.03
% 7.44/2.58  Main loop            : 1.47
% 7.44/2.58  Inferencing          : 0.46
% 7.44/2.58  Reduction            : 0.47
% 7.44/2.58  Demodulation         : 0.31
% 7.44/2.58  BG Simplification    : 0.07
% 7.44/2.58  Subsumption          : 0.38
% 7.44/2.58  Abstraction          : 0.06
% 7.44/2.58  MUC search           : 0.00
% 7.44/2.58  Cooper               : 0.00
% 7.44/2.58  Total                : 1.84
% 7.44/2.58  Index Insertion      : 0.00
% 7.44/2.58  Index Deletion       : 0.00
% 7.44/2.58  Index Matching       : 0.00
% 7.44/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
