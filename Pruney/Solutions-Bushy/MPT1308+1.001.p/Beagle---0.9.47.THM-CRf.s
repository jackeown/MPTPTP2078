%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1308+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:46 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 128 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 352 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).

tff(f_49,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(c_60,plain,(
    ~ v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_66,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_1,B_10] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_1),B_10),u1_pre_topc(A_1))
      | ~ r1_tarski(B_10,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v2_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k5_setfam_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_167,plain,(
    ! [B_72,A_73] :
      ( v3_pre_topc(B_72,A_73)
      | ~ r2_hidden(B_72,u1_pre_topc(A_73))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_458,plain,(
    ! [A_136,B_137] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_136),B_137),A_136)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(A_136),B_137),u1_pre_topc(A_136))
      | ~ l1_pre_topc(A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_136)))) ) ),
    inference(resolution,[status(thm)],[c_56,c_167])).

tff(c_475,plain,(
    ! [A_140,B_141] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_140),B_141),A_140)
      | ~ r1_tarski(B_141,u1_pre_topc(A_140))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_140))))
      | ~ v2_pre_topc(A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_34,c_458])).

tff(c_487,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_475])).

tff(c_494,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_487])).

tff(c_495,plain,(
    ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_494])).

tff(c_50,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_5'(A_25,B_26),A_25)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden('#skF_5'(A_41,B_42),B_42)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [A_25] : r1_tarski(A_25,A_25) ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_77,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_80,plain,(
    ! [A_25,B_26,B_45] :
      ( r2_hidden('#skF_5'(A_25,B_26),B_45)
      | ~ r1_tarski(A_25,B_45)
      | r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_62,plain,(
    v1_tops_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_85,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_88,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(A_48,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_85])).

tff(c_502,plain,(
    ! [C_147,A_148,B_149] :
      ( v3_pre_topc(C_147,A_148)
      | ~ r2_hidden(C_147,B_149)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ v1_tops_2(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148))))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1233,plain,(
    ! [A_232,B_233,A_234] :
      ( v3_pre_topc('#skF_5'(A_232,B_233),A_234)
      | ~ m1_subset_1('#skF_5'(A_232,B_233),k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ v1_tops_2(A_232,A_234)
      | ~ m1_subset_1(A_232,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234))))
      | ~ l1_pre_topc(A_234)
      | r1_tarski(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_50,c_502])).

tff(c_1253,plain,(
    ! [A_232,B_233] :
      ( v3_pre_topc('#skF_5'(A_232,B_233),'#skF_6')
      | ~ v1_tops_2(A_232,'#skF_6')
      | ~ m1_subset_1(A_232,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))
      | ~ l1_pre_topc('#skF_6')
      | r1_tarski(A_232,B_233)
      | ~ r2_hidden('#skF_5'(A_232,B_233),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_88,c_1233])).

tff(c_1261,plain,(
    ! [A_235,B_236] :
      ( v3_pre_topc('#skF_5'(A_235,B_236),'#skF_6')
      | ~ v1_tops_2(A_235,'#skF_6')
      | ~ m1_subset_1(A_235,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))
      | r1_tarski(A_235,B_236)
      | ~ r2_hidden('#skF_5'(A_235,B_236),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1253])).

tff(c_1284,plain,(
    ! [B_236] :
      ( v3_pre_topc('#skF_5'('#skF_7',B_236),'#skF_6')
      | ~ v1_tops_2('#skF_7','#skF_6')
      | r1_tarski('#skF_7',B_236)
      | ~ r2_hidden('#skF_5'('#skF_7',B_236),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_1261])).

tff(c_1303,plain,(
    ! [B_237] :
      ( v3_pre_topc('#skF_5'('#skF_7',B_237),'#skF_6')
      | r1_tarski('#skF_7',B_237)
      | ~ r2_hidden('#skF_5'('#skF_7',B_237),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1284])).

tff(c_116,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,u1_pre_topc(A_60))
      | ~ v3_pre_topc(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_123,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc(A_48,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ r2_hidden(A_48,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_88,c_116])).

tff(c_128,plain,(
    ! [A_61] :
      ( r2_hidden(A_61,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc(A_61,'#skF_6')
      | ~ r2_hidden(A_61,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_123])).

tff(c_48,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_5'(A_25,B_26),B_26)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc('#skF_5'(A_25,u1_pre_topc('#skF_6')),'#skF_6')
      | ~ r2_hidden('#skF_5'(A_25,u1_pre_topc('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_128,c_48])).

tff(c_1307,plain,
    ( r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ r2_hidden('#skF_5'('#skF_7',u1_pre_topc('#skF_6')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1303,c_139])).

tff(c_1310,plain,(
    ~ r2_hidden('#skF_5'('#skF_7',u1_pre_topc('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_495,c_1307])).

tff(c_1313,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_1310])).

tff(c_1319,plain,(
    r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1313])).

tff(c_1321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_1319])).

%------------------------------------------------------------------------------
