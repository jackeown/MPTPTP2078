%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:18 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 267 expanded)
%              Number of leaves         :   31 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 764 expanded)
%              Number of equality atoms :    7 (  36 expanded)
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

tff(f_109,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_77,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_91,axiom,(
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

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_87,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_16])).

tff(c_93,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_90])).

tff(c_97,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_97])).

tff(c_102,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_38,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_57,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_104,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_57])).

tff(c_44,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_109,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_44])).

tff(c_110,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_109])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_213,plain,(
    ! [B_71,A_72,C_73] :
      ( r2_hidden(B_71,k1_tops_1(A_72,C_73))
      | ~ m1_connsp_2(C_73,A_72,B_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(B_71,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_219,plain,(
    ! [B_71,A_72,A_6] :
      ( r2_hidden(B_71,k1_tops_1(A_72,A_6))
      | ~ m1_connsp_2(A_6,A_72,B_71)
      | ~ m1_subset_1(B_71,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72)
      | ~ r1_tarski(A_6,u1_struct_0(A_72)) ) ),
    inference(resolution,[status(thm)],[c_12,c_213])).

tff(c_103,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [C_54,A_55,B_56] :
      ( m2_connsp_2(C_54,A_55,B_56)
      | ~ r1_tarski(B_56,k1_tops_1(A_55,C_54))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_235,plain,(
    ! [C_78,A_79,A_80] :
      ( m2_connsp_2(C_78,A_79,k1_tarski(A_80))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(k1_tarski(A_80),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | ~ r2_hidden(A_80,k1_tops_1(A_79,C_78)) ) ),
    inference(resolution,[status(thm)],[c_6,c_155])).

tff(c_240,plain,(
    ! [A_80] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_80))
      | ~ m1_subset_1(k1_tarski(A_80),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(A_80,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_28,c_235])).

tff(c_245,plain,(
    ! [A_81] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_81))
      | ~ m1_subset_1(k1_tarski(A_81),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_81,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_240])).

tff(c_250,plain,(
    ! [A_82] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_82))
      | ~ r2_hidden(A_82,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k1_tarski(A_82),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_245])).

tff(c_256,plain,(
    ! [A_83] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_83))
      | ~ r2_hidden(A_83,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_83,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_250])).

tff(c_264,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_256,c_104])).

tff(c_265,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_268,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_265])).

tff(c_271,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_268])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_271])).

tff(c_274,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_278,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_219,c_274])).

tff(c_287,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34,c_32,c_30,c_110,c_278])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_287])).

tff(c_290,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_310,plain,(
    ! [A_92,B_93] :
      ( k6_domain_1(A_92,B_93) = k1_tarski(B_93)
      | ~ m1_subset_1(B_93,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_322,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_310])).

tff(c_323,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_326,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_323,c_16])).

tff(c_329,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_326])).

tff(c_332,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_329])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_332])).

tff(c_338,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_337,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_291,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_344,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_291])).

tff(c_359,plain,(
    ! [B_99,A_100,C_101] :
      ( r1_tarski(B_99,k1_tops_1(A_100,C_101))
      | ~ m2_connsp_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_364,plain,(
    ! [B_99] :
      ( r1_tarski(B_99,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_359])).

tff(c_369,plain,(
    ! [B_102] :
      ( r1_tarski(B_102,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_364])).

tff(c_385,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',A_106)
      | ~ r1_tarski(A_106,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_369])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | ~ r1_tarski(k1_tarski(A_2),B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_396,plain,(
    ! [A_107] :
      ( r2_hidden(A_107,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_107))
      | ~ r1_tarski(k1_tarski(A_107),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_385,c_4])).

tff(c_402,plain,(
    ! [A_108] :
      ( r2_hidden(A_108,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_108))
      | ~ r2_hidden(A_108,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_396])).

tff(c_406,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_344,c_402])).

tff(c_407,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_410,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_407])).

tff(c_413,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_410])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_413])).

tff(c_416,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_20,plain,(
    ! [C_18,A_12,B_16] :
      ( m1_connsp_2(C_18,A_12,B_16)
      | ~ r2_hidden(B_16,k1_tops_1(A_12,C_18))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_16,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_419,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_416,c_20])).

tff(c_422,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_419])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_290,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.42  
% 2.61/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.42  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.61/1.42  
% 2.61/1.42  %Foreground sorts:
% 2.61/1.42  
% 2.61/1.42  
% 2.61/1.42  %Background operators:
% 2.61/1.42  
% 2.61/1.42  
% 2.61/1.42  %Foreground operators:
% 2.61/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.42  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.61/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.61/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.42  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.61/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.61/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.42  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.61/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.42  
% 2.61/1.44  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 2.61/1.44  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.44  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.61/1.44  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.61/1.44  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.61/1.44  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.61/1.44  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.61/1.44  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.61/1.44  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.61/1.44  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.44  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.44  tff(c_64, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.44  tff(c_72, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.61/1.44  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.44  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.44  tff(c_30, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.44  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.44  tff(c_74, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.44  tff(c_86, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.61/1.44  tff(c_87, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_86])).
% 2.61/1.44  tff(c_16, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.44  tff(c_90, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_87, c_16])).
% 2.61/1.44  tff(c_93, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_90])).
% 2.61/1.44  tff(c_97, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_93])).
% 2.61/1.44  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_97])).
% 2.61/1.44  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_86])).
% 2.61/1.44  tff(c_38, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.44  tff(c_57, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.61/1.44  tff(c_104, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_57])).
% 2.61/1.44  tff(c_44, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.61/1.44  tff(c_109, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_44])).
% 2.61/1.44  tff(c_110, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_104, c_109])).
% 2.61/1.44  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.44  tff(c_213, plain, (![B_71, A_72, C_73]: (r2_hidden(B_71, k1_tops_1(A_72, C_73)) | ~m1_connsp_2(C_73, A_72, B_71) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(B_71, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.44  tff(c_219, plain, (![B_71, A_72, A_6]: (r2_hidden(B_71, k1_tops_1(A_72, A_6)) | ~m1_connsp_2(A_6, A_72, B_71) | ~m1_subset_1(B_71, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72) | ~r1_tarski(A_6, u1_struct_0(A_72)))), inference(resolution, [status(thm)], [c_12, c_213])).
% 2.61/1.44  tff(c_103, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_86])).
% 2.61/1.44  tff(c_8, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.44  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.44  tff(c_155, plain, (![C_54, A_55, B_56]: (m2_connsp_2(C_54, A_55, B_56) | ~r1_tarski(B_56, k1_tops_1(A_55, C_54)) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.44  tff(c_235, plain, (![C_78, A_79, A_80]: (m2_connsp_2(C_78, A_79, k1_tarski(A_80)) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(k1_tarski(A_80), k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | ~r2_hidden(A_80, k1_tops_1(A_79, C_78)))), inference(resolution, [status(thm)], [c_6, c_155])).
% 2.61/1.44  tff(c_240, plain, (![A_80]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_80)) | ~m1_subset_1(k1_tarski(A_80), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(A_80, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_28, c_235])).
% 2.61/1.44  tff(c_245, plain, (![A_81]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_81)) | ~m1_subset_1(k1_tarski(A_81), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_81, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_240])).
% 2.61/1.44  tff(c_250, plain, (![A_82]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_82)) | ~r2_hidden(A_82, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tarski(A_82), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_245])).
% 2.61/1.44  tff(c_256, plain, (![A_83]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_83)) | ~r2_hidden(A_83, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_83, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_250])).
% 2.61/1.44  tff(c_264, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_256, c_104])).
% 2.61/1.44  tff(c_265, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_264])).
% 2.61/1.44  tff(c_268, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_265])).
% 2.61/1.44  tff(c_271, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_268])).
% 2.61/1.44  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_271])).
% 2.61/1.44  tff(c_274, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_264])).
% 2.61/1.44  tff(c_278, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_219, c_274])).
% 2.61/1.44  tff(c_287, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34, c_32, c_30, c_110, c_278])).
% 2.61/1.44  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_287])).
% 2.61/1.44  tff(c_290, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.61/1.44  tff(c_310, plain, (![A_92, B_93]: (k6_domain_1(A_92, B_93)=k1_tarski(B_93) | ~m1_subset_1(B_93, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.44  tff(c_322, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_310])).
% 2.61/1.44  tff(c_323, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_322])).
% 2.61/1.44  tff(c_326, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_323, c_16])).
% 2.61/1.44  tff(c_329, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_326])).
% 2.61/1.44  tff(c_332, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_329])).
% 2.61/1.44  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_332])).
% 2.61/1.44  tff(c_338, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_322])).
% 2.61/1.44  tff(c_337, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_322])).
% 2.61/1.44  tff(c_291, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 2.61/1.44  tff(c_344, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_291])).
% 2.61/1.44  tff(c_359, plain, (![B_99, A_100, C_101]: (r1_tarski(B_99, k1_tops_1(A_100, C_101)) | ~m2_connsp_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.44  tff(c_364, plain, (![B_99]: (r1_tarski(B_99, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_359])).
% 2.61/1.44  tff(c_369, plain, (![B_102]: (r1_tarski(B_102, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_364])).
% 2.61/1.44  tff(c_385, plain, (![A_106]: (r1_tarski(A_106, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', A_106) | ~r1_tarski(A_106, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_369])).
% 2.61/1.44  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | ~r1_tarski(k1_tarski(A_2), B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.44  tff(c_396, plain, (![A_107]: (r2_hidden(A_107, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_107)) | ~r1_tarski(k1_tarski(A_107), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_385, c_4])).
% 2.61/1.44  tff(c_402, plain, (![A_108]: (r2_hidden(A_108, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_108)) | ~r2_hidden(A_108, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_396])).
% 2.61/1.44  tff(c_406, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_344, c_402])).
% 2.61/1.44  tff(c_407, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_406])).
% 2.61/1.44  tff(c_410, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_407])).
% 2.61/1.44  tff(c_413, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_410])).
% 2.61/1.44  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_413])).
% 2.61/1.44  tff(c_416, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_406])).
% 2.61/1.44  tff(c_20, plain, (![C_18, A_12, B_16]: (m1_connsp_2(C_18, A_12, B_16) | ~r2_hidden(B_16, k1_tops_1(A_12, C_18)) | ~m1_subset_1(C_18, k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_16, u1_struct_0(A_12)) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.44  tff(c_419, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_416, c_20])).
% 2.61/1.44  tff(c_422, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_419])).
% 2.61/1.44  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_290, c_422])).
% 2.61/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.44  
% 2.61/1.44  Inference rules
% 2.61/1.44  ----------------------
% 2.61/1.44  #Ref     : 0
% 2.61/1.44  #Sup     : 70
% 2.61/1.44  #Fact    : 0
% 2.61/1.44  #Define  : 0
% 2.61/1.44  #Split   : 9
% 2.61/1.44  #Chain   : 0
% 2.61/1.44  #Close   : 0
% 2.61/1.44  
% 2.61/1.44  Ordering : KBO
% 2.61/1.44  
% 2.61/1.44  Simplification rules
% 2.61/1.44  ----------------------
% 2.61/1.44  #Subsume      : 2
% 2.61/1.44  #Demod        : 41
% 2.61/1.44  #Tautology    : 24
% 2.61/1.44  #SimpNegUnit  : 11
% 2.61/1.44  #BackRed      : 2
% 2.61/1.44  
% 2.61/1.44  #Partial instantiations: 0
% 2.61/1.44  #Strategies tried      : 1
% 2.61/1.44  
% 2.61/1.44  Timing (in seconds)
% 2.61/1.44  ----------------------
% 2.61/1.44  Preprocessing        : 0.33
% 2.61/1.44  Parsing              : 0.18
% 2.61/1.44  CNF conversion       : 0.02
% 2.61/1.45  Main loop            : 0.27
% 2.61/1.45  Inferencing          : 0.11
% 2.61/1.45  Reduction            : 0.08
% 2.61/1.45  Demodulation         : 0.05
% 2.61/1.45  BG Simplification    : 0.02
% 2.61/1.45  Subsumption          : 0.04
% 2.61/1.45  Abstraction          : 0.02
% 2.61/1.45  MUC search           : 0.00
% 2.61/1.45  Cooper               : 0.00
% 2.61/1.45  Total                : 0.64
% 2.61/1.45  Index Insertion      : 0.00
% 2.61/1.45  Index Deletion       : 0.00
% 2.61/1.45  Index Matching       : 0.00
% 2.61/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
