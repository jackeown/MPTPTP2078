%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1383+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:53 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 751 expanded)
%              Number of leaves         :   22 ( 279 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 (3741 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_41,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_47,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_49,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_46,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_131,plain,(
    ! [B_72,A_73,C_74,D_75] :
      ( r2_hidden(B_72,k1_tops_1(A_73,C_74))
      | ~ r2_hidden(B_72,D_75)
      | ~ r1_tarski(D_75,C_74)
      | ~ v3_pre_topc(D_75,A_73)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_147,plain,(
    ! [A_76,C_77] :
      ( r2_hidden('#skF_3',k1_tops_1(A_76,C_77))
      | ~ r1_tarski('#skF_5',C_77)
      | ~ v3_pre_topc('#skF_5',A_76)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_48,c_131])).

tff(c_149,plain,(
    ! [C_77] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_77))
      | ~ r1_tarski('#skF_5',C_77)
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_153,plain,(
    ! [C_78] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_78))
      | ~ r1_tarski('#skF_5',C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_47,c_149])).

tff(c_163,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_170,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_163])).

tff(c_2,plain,(
    ! [C_7,A_1,B_5] :
      ( m1_connsp_2(C_7,A_1,B_5)
      | ~ r2_hidden(B_5,k1_tops_1(A_1,C_7))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_5,u1_struct_0(A_1))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_174,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_182,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_174])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_54,c_182])).

tff(c_188,plain,(
    ! [D_79] :
      ( ~ r2_hidden('#skF_3',D_79)
      | ~ r1_tarski(D_79,'#skF_4')
      | ~ v3_pre_topc(D_79,'#skF_2')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_191,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_188])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_49,c_48,c_191])).

tff(c_199,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_241,plain,(
    ! [B_100,A_101,C_102] :
      ( r2_hidden(B_100,k1_tops_1(A_101,C_102))
      | ~ m1_connsp_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_100,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_245,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_100)
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_241])).

tff(c_249,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_100)
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_245])).

tff(c_251,plain,(
    ! [B_103] :
      ( r2_hidden(B_103,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_249])).

tff(c_12,plain,(
    ! [A_12,B_19,C_20] :
      ( r1_tarski('#skF_1'(A_12,B_19,C_20),C_20)
      | ~ r2_hidden(B_19,k1_tops_1(A_12,C_20))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_257,plain,(
    ! [B_103] :
      ( r1_tarski('#skF_1'('#skF_2',B_103,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_251,c_12])).

tff(c_267,plain,(
    ! [B_103] :
      ( r1_tarski('#skF_1'('#skF_2',B_103,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_257])).

tff(c_250,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_100)
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_249])).

tff(c_10,plain,(
    ! [B_19,A_12,C_20] :
      ( r2_hidden(B_19,'#skF_1'(A_12,B_19,C_20))
      | ~ r2_hidden(B_19,k1_tops_1(A_12,C_20))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_255,plain,(
    ! [B_103] :
      ( r2_hidden(B_103,'#skF_1'('#skF_2',B_103,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_251,c_10])).

tff(c_264,plain,(
    ! [B_103] :
      ( r2_hidden(B_103,'#skF_1'('#skF_2',B_103,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_103)
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_255])).

tff(c_221,plain,(
    ! [A_87,B_88,C_89] :
      ( v3_pre_topc('#skF_1'(A_87,B_88,C_89),A_87)
      | ~ r2_hidden(B_88,k1_tops_1(A_87,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_223,plain,(
    ! [B_88] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_88,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_88,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_221])).

tff(c_226,plain,(
    ! [B_88] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_88,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_88,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_223])).

tff(c_229,plain,(
    ! [A_94,B_95,C_96] :
      ( m1_subset_1('#skF_1'(A_94,B_95,C_96),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ r2_hidden(B_95,k1_tops_1(A_94,C_96))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_205,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_28])).

tff(c_235,plain,(
    ! [B_95,C_96] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_95,C_96))
      | ~ r1_tarski('#skF_1'('#skF_2',B_95,C_96),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_95,C_96),'#skF_2')
      | ~ r2_hidden(B_95,k1_tops_1('#skF_2',C_96))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_229,c_205])).

tff(c_281,plain,(
    ! [B_112,C_113] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_112,C_113))
      | ~ r1_tarski('#skF_1'('#skF_2',B_112,C_113),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_112,C_113),'#skF_2')
      | ~ r2_hidden(B_112,k1_tops_1('#skF_2',C_113))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_235])).

tff(c_283,plain,(
    ! [B_88] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_88,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_88,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_88,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_226,c_281])).

tff(c_287,plain,(
    ! [B_114] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_114,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_114,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_114,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_283])).

tff(c_290,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_264,c_287])).

tff(c_293,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_199,c_290])).

tff(c_301,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_304,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_250,c_301])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_199,c_304])).

tff(c_309,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_333,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_267,c_309])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_199,c_333])).

tff(c_338,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_380,plain,(
    ! [B_142,A_143,C_144] :
      ( r2_hidden(B_142,k1_tops_1(A_143,C_144))
      | ~ m1_connsp_2(C_144,A_143,B_142)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(B_142,u1_struct_0(A_143))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_384,plain,(
    ! [B_142] :
      ( r2_hidden(B_142,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_142)
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_380])).

tff(c_388,plain,(
    ! [B_142] :
      ( r2_hidden(B_142,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_142)
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_384])).

tff(c_390,plain,(
    ! [B_145] :
      ( r2_hidden(B_145,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_145)
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_388])).

tff(c_396,plain,(
    ! [B_145] :
      ( r1_tarski('#skF_1'('#skF_2',B_145,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_145)
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_390,c_12])).

tff(c_406,plain,(
    ! [B_145] :
      ( r1_tarski('#skF_1'('#skF_2',B_145,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_145)
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_396])).

tff(c_389,plain,(
    ! [B_142] :
      ( r2_hidden(B_142,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_142)
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_388])).

tff(c_394,plain,(
    ! [B_145] :
      ( r2_hidden(B_145,'#skF_1'('#skF_2',B_145,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_145)
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_390,c_10])).

tff(c_403,plain,(
    ! [B_145] :
      ( r2_hidden(B_145,'#skF_1'('#skF_2',B_145,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_145)
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_394])).

tff(c_360,plain,(
    ! [A_129,B_130,C_131] :
      ( v3_pre_topc('#skF_1'(A_129,B_130,C_131),A_129)
      | ~ r2_hidden(B_130,k1_tops_1(A_129,C_131))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_362,plain,(
    ! [B_130] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_130,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_130,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_360])).

tff(c_365,plain,(
    ! [B_130] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_130,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_130,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_362])).

tff(c_368,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1('#skF_1'(A_136,B_137,C_138),k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ r2_hidden(B_137,k1_tops_1(A_136,C_138))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_339,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_343,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_36])).

tff(c_374,plain,(
    ! [B_137,C_138] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_137,C_138))
      | ~ r1_tarski('#skF_1'('#skF_2',B_137,C_138),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_137,C_138),'#skF_2')
      | ~ r2_hidden(B_137,k1_tops_1('#skF_2',C_138))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_368,c_343])).

tff(c_420,plain,(
    ! [B_154,C_155] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_154,C_155))
      | ~ r1_tarski('#skF_1'('#skF_2',B_154,C_155),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_154,C_155),'#skF_2')
      | ~ r2_hidden(B_154,k1_tops_1('#skF_2',C_155))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_374])).

tff(c_422,plain,(
    ! [B_130] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_130,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_130,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_130,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_365,c_420])).

tff(c_433,plain,(
    ! [B_160] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_160,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_160,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_160,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_422])).

tff(c_436,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_403,c_433])).

tff(c_439,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_338,c_436])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_443,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_389,c_440])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_338,c_443])).

tff(c_448,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_472,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_406,c_448])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_338,c_472])).

tff(c_477,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_645,plain,(
    ! [B_220,A_221,C_222] :
      ( r2_hidden(B_220,k1_tops_1(A_221,C_222))
      | ~ m1_connsp_2(C_222,A_221,B_220)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_subset_1(B_220,u1_struct_0(A_221))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_649,plain,(
    ! [B_220] :
      ( r2_hidden(B_220,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_220)
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_645])).

tff(c_653,plain,(
    ! [B_220] :
      ( r2_hidden(B_220,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_220)
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_649])).

tff(c_655,plain,(
    ! [B_223] :
      ( r2_hidden(B_223,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_223)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_653])).

tff(c_659,plain,(
    ! [B_223] :
      ( r1_tarski('#skF_1'('#skF_2',B_223,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_223)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_655,c_12])).

tff(c_668,plain,(
    ! [B_223] :
      ( r1_tarski('#skF_1'('#skF_2',B_223,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_223)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_659])).

tff(c_654,plain,(
    ! [B_220] :
      ( r2_hidden(B_220,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_220)
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_653])).

tff(c_661,plain,(
    ! [B_223] :
      ( r2_hidden(B_223,'#skF_1'('#skF_2',B_223,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_223)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_655,c_10])).

tff(c_671,plain,(
    ! [B_223] :
      ( r2_hidden(B_223,'#skF_1'('#skF_2',B_223,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_223)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_661])).

tff(c_624,plain,(
    ! [A_204,B_205,C_206] :
      ( v3_pre_topc('#skF_1'(A_204,B_205,C_206),A_204)
      | ~ r2_hidden(B_205,k1_tops_1(A_204,C_206))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_626,plain,(
    ! [B_205] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_205,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_205,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_624])).

tff(c_629,plain,(
    ! [B_205] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_205,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_205,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_626])).

tff(c_633,plain,(
    ! [A_214,B_215,C_216] :
      ( m1_subset_1('#skF_1'(A_214,B_215,C_216),k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ r2_hidden(B_215,k1_tops_1(A_214,C_216))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_478,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_607,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_32])).

tff(c_639,plain,(
    ! [B_215,C_216] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_215,C_216))
      | ~ r1_tarski('#skF_1'('#skF_2',B_215,C_216),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_215,C_216),'#skF_2')
      | ~ r2_hidden(B_215,k1_tops_1('#skF_2',C_216))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_633,c_607])).

tff(c_681,plain,(
    ! [B_230,C_231] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_230,C_231))
      | ~ r1_tarski('#skF_1'('#skF_2',B_230,C_231),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_230,C_231),'#skF_2')
      | ~ r2_hidden(B_230,k1_tops_1('#skF_2',C_231))
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_639])).

tff(c_683,plain,(
    ! [B_205] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_205,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_205,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_205,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_629,c_681])).

tff(c_687,plain,(
    ! [B_232] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_232,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_232,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_232,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_683])).

tff(c_690,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_671,c_687])).

tff(c_693,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_477,c_690])).

tff(c_694,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_693])).

tff(c_704,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_654,c_694])).

tff(c_708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_477,c_704])).

tff(c_709,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_693])).

tff(c_732,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_668,c_709])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_477,c_732])).

tff(c_737,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_888,plain,(
    ! [B_286,A_287,C_288] :
      ( r2_hidden(B_286,k1_tops_1(A_287,C_288))
      | ~ m1_connsp_2(C_288,A_287,B_286)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ m1_subset_1(B_286,u1_struct_0(A_287))
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_892,plain,(
    ! [B_286] :
      ( r2_hidden(B_286,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_286)
      | ~ m1_subset_1(B_286,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_888])).

tff(c_896,plain,(
    ! [B_286] :
      ( r2_hidden(B_286,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_286)
      | ~ m1_subset_1(B_286,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_892])).

tff(c_898,plain,(
    ! [B_289] :
      ( r2_hidden(B_289,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_896])).

tff(c_904,plain,(
    ! [B_289] :
      ( r1_tarski('#skF_1'('#skF_2',B_289,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_898,c_12])).

tff(c_914,plain,(
    ! [B_289] :
      ( r1_tarski('#skF_1'('#skF_2',B_289,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_904])).

tff(c_897,plain,(
    ! [B_286] :
      ( r2_hidden(B_286,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_286)
      | ~ m1_subset_1(B_286,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_896])).

tff(c_902,plain,(
    ! [B_289] :
      ( r2_hidden(B_289,'#skF_1'('#skF_2',B_289,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_898,c_10])).

tff(c_911,plain,(
    ! [B_289] :
      ( r2_hidden(B_289,'#skF_1'('#skF_2',B_289,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_902])).

tff(c_868,plain,(
    ! [A_273,B_274,C_275] :
      ( v3_pre_topc('#skF_1'(A_273,B_274,C_275),A_273)
      | ~ r2_hidden(B_274,k1_tops_1(A_273,C_275))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_870,plain,(
    ! [B_274] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_274,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_274,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_868])).

tff(c_873,plain,(
    ! [B_274] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_274,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_274,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_870])).

tff(c_876,plain,(
    ! [A_280,B_281,C_282] :
      ( m1_subset_1('#skF_1'(A_280,B_281,C_282),k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ r2_hidden(B_281,k1_tops_1(A_280,C_282))
      | ~ m1_subset_1(C_282,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_738,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_851,plain,(
    ! [D_42] :
      ( ~ r2_hidden('#skF_3',D_42)
      | ~ r1_tarski(D_42,'#skF_4')
      | ~ v3_pre_topc(D_42,'#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_40])).

tff(c_882,plain,(
    ! [B_281,C_282] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_281,C_282))
      | ~ r1_tarski('#skF_1'('#skF_2',B_281,C_282),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_281,C_282),'#skF_2')
      | ~ r2_hidden(B_281,k1_tops_1('#skF_2',C_282))
      | ~ m1_subset_1(C_282,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_876,c_851])).

tff(c_929,plain,(
    ! [B_301,C_302] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_301,C_302))
      | ~ r1_tarski('#skF_1'('#skF_2',B_301,C_302),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_301,C_302),'#skF_2')
      | ~ r2_hidden(B_301,k1_tops_1('#skF_2',C_302))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_882])).

tff(c_931,plain,(
    ! [B_274] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_274,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_274,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_274,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_873,c_929])).

tff(c_935,plain,(
    ! [B_303] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_303,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_303,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_303,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_931])).

tff(c_938,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_911,c_935])).

tff(c_941,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_737,c_938])).

tff(c_942,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_941])).

tff(c_945,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_897,c_942])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_737,c_945])).

tff(c_950,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_941])).

tff(c_980,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_914,c_950])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_737,c_980])).

%------------------------------------------------------------------------------
