%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:18 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 249 expanded)
%              Number of leaves         :   32 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 ( 715 expanded)
%              Number of equality atoms :    9 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
                <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_79,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_61,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_101,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_48])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_188,plain,(
    ! [B_81,A_82,C_83] :
      ( r2_hidden(B_81,k1_tops_1(A_82,C_83))
      | ~ m1_connsp_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_81,u1_struct_0(A_82))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_193,plain,(
    ! [B_81] :
      ( r2_hidden(B_81,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_81)
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_188])).

tff(c_197,plain,(
    ! [B_81] :
      ( r2_hidden(B_81,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_81)
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_193])).

tff(c_198,plain,(
    ! [B_81] :
      ( r2_hidden(B_81,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_81)
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_197])).

tff(c_14,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_72])).

tff(c_85,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_16])).

tff(c_91,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_88])).

tff(c_94,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_94])).

tff(c_100,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(k2_tarski(A_56,B_57),C_58)
      | ~ r2_hidden(B_57,C_58)
      | ~ r2_hidden(A_56,C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_116,plain,(
    ! [A_1,C_58] :
      ( r1_tarski(k1_tarski(A_1),C_58)
      | ~ r2_hidden(A_1,C_58)
      | ~ r2_hidden(A_1,C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_142,plain,(
    ! [C_69,A_70,B_71] :
      ( m2_connsp_2(C_69,A_70,B_71)
      | ~ r1_tarski(B_71,k1_tops_1(A_70,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_229,plain,(
    ! [C_91,A_92,A_93] :
      ( m2_connsp_2(C_91,A_92,k1_tarski(A_93))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(k1_tarski(A_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | ~ r2_hidden(A_93,k1_tops_1(A_92,C_91)) ) ),
    inference(resolution,[status(thm)],[c_116,c_142])).

tff(c_234,plain,(
    ! [A_93] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_93))
      | ~ m1_subset_1(k1_tarski(A_93),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(A_93,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_229])).

tff(c_239,plain,(
    ! [A_94] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_94))
      | ~ m1_subset_1(k1_tarski(A_94),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_94,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_234])).

tff(c_245,plain,(
    ! [A_95] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_95))
      | ~ r2_hidden(A_95,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_95,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_99,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_102,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_61])).

tff(c_258,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_245,c_102])).

tff(c_270,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_273,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_270])).

tff(c_276,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_273])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_276])).

tff(c_279,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_284,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_198,c_279])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_101,c_284])).

tff(c_292,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_304,plain,(
    ! [A_109,B_110] :
      ( k6_domain_1(A_109,B_110) = k1_tarski(B_110)
      | ~ m1_subset_1(B_110,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_316,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_304])).

tff(c_319,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_322,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_319,c_16])).

tff(c_325,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_322])).

tff(c_328,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_325])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_328])).

tff(c_334,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_333,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_293,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_335,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_293])).

tff(c_383,plain,(
    ! [B_127,A_128,C_129] :
      ( r1_tarski(B_127,k1_tops_1(A_128,C_129))
      | ~ m2_connsp_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_388,plain,(
    ! [B_127] :
      ( r1_tarski(B_127,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_383])).

tff(c_405,plain,(
    ! [B_134] :
      ( r1_tarski(B_134,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_388])).

tff(c_416,plain,(
    ! [A_135] :
      ( r1_tarski(k1_tarski(A_135),k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_135))
      | ~ r2_hidden(A_135,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_405])).

tff(c_294,plain,(
    ! [B_99,C_100,A_101] :
      ( r2_hidden(B_99,C_100)
      | ~ r1_tarski(k2_tarski(A_101,B_99),C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_297,plain,(
    ! [A_1,C_100] :
      ( r2_hidden(A_1,C_100)
      | ~ r1_tarski(k1_tarski(A_1),C_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_294])).

tff(c_426,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_136))
      | ~ r2_hidden(A_136,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_416,c_297])).

tff(c_430,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_335,c_426])).

tff(c_431,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_434,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_431])).

tff(c_437,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_434])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_437])).

tff(c_440,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_20,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_connsp_2(C_19,A_13,B_17)
      | ~ r2_hidden(B_17,k1_tops_1(A_13,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_454,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_440,c_20])).

tff(c_457,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_454])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_292,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:27:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.42  
% 2.65/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.42  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.65/1.42  
% 2.65/1.42  %Foreground sorts:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Background operators:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Foreground operators:
% 2.65/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.42  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.65/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.42  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.42  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.65/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.42  
% 2.65/1.44  tff(f_136, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 2.65/1.44  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.65/1.44  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.65/1.44  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.65/1.44  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.65/1.44  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.65/1.44  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.65/1.44  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.65/1.44  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.65/1.44  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.65/1.44  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.44  tff(c_34, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.44  tff(c_42, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.44  tff(c_61, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.65/1.44  tff(c_48, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.44  tff(c_101, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_61, c_48])).
% 2.65/1.44  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.44  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.44  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.65/1.44  tff(c_188, plain, (![B_81, A_82, C_83]: (r2_hidden(B_81, k1_tops_1(A_82, C_83)) | ~m1_connsp_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_81, u1_struct_0(A_82)) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.44  tff(c_193, plain, (![B_81]: (r2_hidden(B_81, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_81) | ~m1_subset_1(B_81, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_188])).
% 2.65/1.44  tff(c_197, plain, (![B_81]: (r2_hidden(B_81, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_81) | ~m1_subset_1(B_81, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_193])).
% 2.65/1.44  tff(c_198, plain, (![B_81]: (r2_hidden(B_81, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_81) | ~m1_subset_1(B_81, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_197])).
% 2.65/1.44  tff(c_14, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.44  tff(c_72, plain, (![A_54, B_55]: (k6_domain_1(A_54, B_55)=k1_tarski(B_55) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.65/1.44  tff(c_84, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_72])).
% 2.65/1.44  tff(c_85, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.65/1.44  tff(c_16, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.44  tff(c_88, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_85, c_16])).
% 2.65/1.44  tff(c_91, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_88])).
% 2.65/1.44  tff(c_94, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_91])).
% 2.65/1.44  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_94])).
% 2.65/1.44  tff(c_100, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_84])).
% 2.65/1.44  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.44  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.44  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.44  tff(c_107, plain, (![A_56, B_57, C_58]: (r1_tarski(k2_tarski(A_56, B_57), C_58) | ~r2_hidden(B_57, C_58) | ~r2_hidden(A_56, C_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.44  tff(c_116, plain, (![A_1, C_58]: (r1_tarski(k1_tarski(A_1), C_58) | ~r2_hidden(A_1, C_58) | ~r2_hidden(A_1, C_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 2.65/1.44  tff(c_142, plain, (![C_69, A_70, B_71]: (m2_connsp_2(C_69, A_70, B_71) | ~r1_tarski(B_71, k1_tops_1(A_70, C_69)) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.65/1.44  tff(c_229, plain, (![C_91, A_92, A_93]: (m2_connsp_2(C_91, A_92, k1_tarski(A_93)) | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(k1_tarski(A_93), k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | ~r2_hidden(A_93, k1_tops_1(A_92, C_91)))), inference(resolution, [status(thm)], [c_116, c_142])).
% 2.65/1.44  tff(c_234, plain, (![A_93]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_93)) | ~m1_subset_1(k1_tarski(A_93), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(A_93, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_32, c_229])).
% 2.65/1.44  tff(c_239, plain, (![A_94]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_94)) | ~m1_subset_1(k1_tarski(A_94), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_94, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_234])).
% 2.65/1.44  tff(c_245, plain, (![A_95]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_95)) | ~r2_hidden(A_95, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_95, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_239])).
% 2.65/1.44  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_84])).
% 2.65/1.44  tff(c_102, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_61])).
% 2.65/1.44  tff(c_258, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_245, c_102])).
% 2.65/1.44  tff(c_270, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_258])).
% 2.65/1.44  tff(c_273, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_270])).
% 2.65/1.44  tff(c_276, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_273])).
% 2.65/1.44  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_276])).
% 2.65/1.44  tff(c_279, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_258])).
% 2.65/1.44  tff(c_284, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_198, c_279])).
% 2.65/1.44  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_101, c_284])).
% 2.65/1.44  tff(c_292, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.65/1.44  tff(c_304, plain, (![A_109, B_110]: (k6_domain_1(A_109, B_110)=k1_tarski(B_110) | ~m1_subset_1(B_110, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.65/1.44  tff(c_316, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_304])).
% 2.65/1.44  tff(c_319, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_316])).
% 2.65/1.44  tff(c_322, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_319, c_16])).
% 2.65/1.44  tff(c_325, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_322])).
% 2.65/1.44  tff(c_328, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_325])).
% 2.65/1.44  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_328])).
% 2.65/1.44  tff(c_334, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_316])).
% 2.65/1.44  tff(c_333, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_316])).
% 2.65/1.44  tff(c_293, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.65/1.44  tff(c_335, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_293])).
% 2.65/1.44  tff(c_383, plain, (![B_127, A_128, C_129]: (r1_tarski(B_127, k1_tops_1(A_128, C_129)) | ~m2_connsp_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.65/1.44  tff(c_388, plain, (![B_127]: (r1_tarski(B_127, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_383])).
% 2.65/1.44  tff(c_405, plain, (![B_134]: (r1_tarski(B_134, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_388])).
% 2.65/1.44  tff(c_416, plain, (![A_135]: (r1_tarski(k1_tarski(A_135), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_135)) | ~r2_hidden(A_135, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_405])).
% 2.65/1.44  tff(c_294, plain, (![B_99, C_100, A_101]: (r2_hidden(B_99, C_100) | ~r1_tarski(k2_tarski(A_101, B_99), C_100))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.44  tff(c_297, plain, (![A_1, C_100]: (r2_hidden(A_1, C_100) | ~r1_tarski(k1_tarski(A_1), C_100))), inference(superposition, [status(thm), theory('equality')], [c_2, c_294])).
% 2.65/1.44  tff(c_426, plain, (![A_136]: (r2_hidden(A_136, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_136)) | ~r2_hidden(A_136, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_416, c_297])).
% 2.65/1.44  tff(c_430, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_335, c_426])).
% 2.65/1.44  tff(c_431, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_430])).
% 2.65/1.44  tff(c_434, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_431])).
% 2.65/1.44  tff(c_437, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_434])).
% 2.65/1.44  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_437])).
% 2.65/1.44  tff(c_440, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_430])).
% 2.65/1.44  tff(c_20, plain, (![C_19, A_13, B_17]: (m1_connsp_2(C_19, A_13, B_17) | ~r2_hidden(B_17, k1_tops_1(A_13, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, u1_struct_0(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.44  tff(c_454, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_440, c_20])).
% 2.65/1.44  tff(c_457, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_454])).
% 2.65/1.44  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_292, c_457])).
% 2.65/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.44  
% 2.65/1.44  Inference rules
% 2.65/1.44  ----------------------
% 2.65/1.44  #Ref     : 0
% 2.65/1.44  #Sup     : 77
% 2.65/1.44  #Fact    : 0
% 2.65/1.44  #Define  : 0
% 2.65/1.44  #Split   : 10
% 2.65/1.44  #Chain   : 0
% 2.65/1.44  #Close   : 0
% 2.65/1.44  
% 2.65/1.44  Ordering : KBO
% 2.65/1.44  
% 2.65/1.44  Simplification rules
% 2.65/1.44  ----------------------
% 2.65/1.44  #Subsume      : 2
% 2.65/1.44  #Demod        : 47
% 2.65/1.44  #Tautology    : 29
% 2.65/1.44  #SimpNegUnit  : 13
% 2.65/1.44  #BackRed      : 2
% 2.65/1.44  
% 2.65/1.44  #Partial instantiations: 0
% 2.65/1.44  #Strategies tried      : 1
% 2.65/1.44  
% 2.65/1.44  Timing (in seconds)
% 2.65/1.44  ----------------------
% 2.65/1.44  Preprocessing        : 0.35
% 2.65/1.44  Parsing              : 0.19
% 2.65/1.44  CNF conversion       : 0.02
% 2.65/1.44  Main loop            : 0.27
% 2.65/1.44  Inferencing          : 0.11
% 2.65/1.44  Reduction            : 0.08
% 2.65/1.44  Demodulation         : 0.05
% 2.65/1.45  BG Simplification    : 0.02
% 2.65/1.45  Subsumption          : 0.04
% 2.65/1.45  Abstraction          : 0.01
% 2.65/1.45  MUC search           : 0.00
% 2.65/1.45  Cooper               : 0.00
% 2.65/1.45  Total                : 0.66
% 2.65/1.45  Index Insertion      : 0.00
% 2.65/1.45  Index Deletion       : 0.00
% 2.65/1.45  Index Matching       : 0.00
% 2.65/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
