%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:17 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 185 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  180 ( 531 expanded)
%              Number of equality atoms :    7 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_104,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_72,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_86,axiom,(
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

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_47,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_185,plain,(
    ! [B_49,A_50,C_51] :
      ( r2_hidden(B_49,k1_tops_1(A_50,C_51))
      | ~ m1_connsp_2(C_51,A_50,B_49)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_49,u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_192,plain,(
    ! [B_49] :
      ( r2_hidden(B_49,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_49)
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_185])).

tff(c_200,plain,(
    ! [B_49] :
      ( r2_hidden(B_49,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_49)
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_192])).

tff(c_201,plain,(
    ! [B_49] :
      ( r2_hidden(B_49,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_49)
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_200])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [A_33,B_34] :
      ( k6_domain_1(A_33,B_34) = k1_tarski(B_34)
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_57,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_57,c_8])).

tff(c_63,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_60])).

tff(c_66,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_71,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_32,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_93,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_47,c_32])).

tff(c_72,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k6_domain_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_85,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_86,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_85])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [C_39,A_40,B_41] :
      ( m2_connsp_2(C_39,A_40,B_41)
      | ~ r1_tarski(B_41,k1_tops_1(A_40,C_39))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_217,plain,(
    ! [C_57,A_58,A_59] :
      ( m2_connsp_2(C_57,A_58,k1_tarski(A_59))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(k1_tarski(A_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | ~ r2_hidden(A_59,k1_tops_1(A_58,C_57)) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_224,plain,(
    ! [A_59] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_59))
      | ~ m1_subset_1(k1_tarski(A_59),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(A_59,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_22,c_217])).

tff(c_232,plain,(
    ! [A_60] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_60))
      | ~ m1_subset_1(k1_tarski(A_60),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_60,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_224])).

tff(c_235,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2'))
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_86,c_232])).

tff(c_238,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_235])).

tff(c_241,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_201,c_238])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_47,c_241])).

tff(c_247,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_248,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_248])).

tff(c_257,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_265,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_257,c_8])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_265])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_271])).

tff(c_276,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_246,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_280,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_246])).

tff(c_277,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_285,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k6_domain_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_291,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_285])).

tff(c_294,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_291])).

tff(c_295,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_294])).

tff(c_331,plain,(
    ! [B_72,A_73,C_74] :
      ( r1_tarski(B_72,k1_tops_1(A_73,C_74))
      | ~ m2_connsp_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_338,plain,(
    ! [B_72] :
      ( r1_tarski(B_72,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_331])).

tff(c_346,plain,(
    ! [B_75] :
      ( r1_tarski(B_75,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_338])).

tff(c_349,plain,
    ( r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_295,c_346])).

tff(c_359,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_349])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | ~ r1_tarski(k1_tarski(A_1),B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_372,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_359,c_2])).

tff(c_421,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_connsp_2(C_84,A_85,B_86)
      | ~ r2_hidden(B_86,k1_tops_1(A_85,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_427,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_372,c_421])).

tff(c_438,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_427])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_247,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:52:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.56  
% 2.70/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.56  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.70/1.56  
% 2.70/1.56  %Foreground sorts:
% 2.70/1.56  
% 2.70/1.56  
% 2.70/1.56  %Background operators:
% 2.70/1.56  
% 2.70/1.56  
% 2.70/1.56  %Foreground operators:
% 2.70/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.70/1.56  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.70/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.56  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.70/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.70/1.56  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.56  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.56  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.70/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.70/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.56  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.70/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.56  
% 2.70/1.58  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 2.70/1.58  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.70/1.58  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.70/1.58  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.70/1.58  tff(f_41, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.70/1.58  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.70/1.58  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.70/1.58  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.70/1.58  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.58  tff(c_24, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.58  tff(c_38, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.58  tff(c_47, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 2.70/1.58  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.58  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.58  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.58  tff(c_185, plain, (![B_49, A_50, C_51]: (r2_hidden(B_49, k1_tops_1(A_50, C_51)) | ~m1_connsp_2(C_51, A_50, B_49) | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_49, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.58  tff(c_192, plain, (![B_49]: (r2_hidden(B_49, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_49) | ~m1_subset_1(B_49, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_185])).
% 2.70/1.58  tff(c_200, plain, (![B_49]: (r2_hidden(B_49, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_49) | ~m1_subset_1(B_49, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_192])).
% 2.70/1.58  tff(c_201, plain, (![B_49]: (r2_hidden(B_49, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_49) | ~m1_subset_1(B_49, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_200])).
% 2.70/1.58  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.58  tff(c_48, plain, (![A_33, B_34]: (k6_domain_1(A_33, B_34)=k1_tarski(B_34) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.58  tff(c_56, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_48])).
% 2.70/1.58  tff(c_57, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.70/1.58  tff(c_8, plain, (![A_4]: (~v1_xboole_0(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.58  tff(c_60, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_57, c_8])).
% 2.70/1.58  tff(c_63, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_30, c_60])).
% 2.70/1.58  tff(c_66, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.70/1.58  tff(c_70, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 2.70/1.58  tff(c_71, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.70/1.58  tff(c_32, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.58  tff(c_93, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_47, c_32])).
% 2.70/1.58  tff(c_72, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_56])).
% 2.70/1.58  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k6_domain_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.58  tff(c_81, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 2.70/1.58  tff(c_85, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_81])).
% 2.70/1.58  tff(c_86, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_72, c_85])).
% 2.70/1.58  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.58  tff(c_120, plain, (![C_39, A_40, B_41]: (m2_connsp_2(C_39, A_40, B_41) | ~r1_tarski(B_41, k1_tops_1(A_40, C_39)) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.70/1.58  tff(c_217, plain, (![C_57, A_58, A_59]: (m2_connsp_2(C_57, A_58, k1_tarski(A_59)) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(k1_tarski(A_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | ~r2_hidden(A_59, k1_tops_1(A_58, C_57)))), inference(resolution, [status(thm)], [c_4, c_120])).
% 2.70/1.58  tff(c_224, plain, (![A_59]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_59)) | ~m1_subset_1(k1_tarski(A_59), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(A_59, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_22, c_217])).
% 2.70/1.58  tff(c_232, plain, (![A_60]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_60)) | ~m1_subset_1(k1_tarski(A_60), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_60, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_224])).
% 2.70/1.58  tff(c_235, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2')) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_86, c_232])).
% 2.70/1.58  tff(c_238, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_93, c_235])).
% 2.70/1.58  tff(c_241, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_201, c_238])).
% 2.70/1.58  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_47, c_241])).
% 2.70/1.58  tff(c_247, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.70/1.58  tff(c_248, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.58  tff(c_256, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_248])).
% 2.70/1.58  tff(c_257, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_256])).
% 2.70/1.58  tff(c_265, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_257, c_8])).
% 2.70/1.58  tff(c_268, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_30, c_265])).
% 2.70/1.58  tff(c_271, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_268])).
% 2.70/1.58  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_271])).
% 2.70/1.58  tff(c_276, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_256])).
% 2.70/1.58  tff(c_246, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 2.70/1.58  tff(c_280, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_246])).
% 2.70/1.58  tff(c_277, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_256])).
% 2.70/1.58  tff(c_285, plain, (![A_65, B_66]: (m1_subset_1(k6_domain_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.58  tff(c_291, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_285])).
% 2.70/1.58  tff(c_294, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_291])).
% 2.70/1.58  tff(c_295, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_277, c_294])).
% 2.70/1.58  tff(c_331, plain, (![B_72, A_73, C_74]: (r1_tarski(B_72, k1_tops_1(A_73, C_74)) | ~m2_connsp_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.70/1.58  tff(c_338, plain, (![B_72]: (r1_tarski(B_72, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_331])).
% 2.70/1.58  tff(c_346, plain, (![B_75]: (r1_tarski(B_75, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_338])).
% 2.70/1.58  tff(c_349, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_295, c_346])).
% 2.70/1.58  tff(c_359, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_349])).
% 2.70/1.58  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | ~r1_tarski(k1_tarski(A_1), B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.58  tff(c_372, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_359, c_2])).
% 2.70/1.58  tff(c_421, plain, (![C_84, A_85, B_86]: (m1_connsp_2(C_84, A_85, B_86) | ~r2_hidden(B_86, k1_tops_1(A_85, C_84)) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.58  tff(c_427, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_372, c_421])).
% 2.70/1.58  tff(c_438, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_427])).
% 2.70/1.58  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_247, c_438])).
% 2.70/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.58  
% 2.70/1.58  Inference rules
% 2.70/1.58  ----------------------
% 2.70/1.58  #Ref     : 0
% 2.70/1.58  #Sup     : 74
% 2.70/1.58  #Fact    : 0
% 2.70/1.58  #Define  : 0
% 2.70/1.58  #Split   : 9
% 2.70/1.58  #Chain   : 0
% 2.70/1.58  #Close   : 0
% 2.70/1.58  
% 2.70/1.58  Ordering : KBO
% 2.70/1.58  
% 2.70/1.58  Simplification rules
% 2.70/1.58  ----------------------
% 2.70/1.58  #Subsume      : 3
% 2.70/1.58  #Demod        : 78
% 2.70/1.58  #Tautology    : 25
% 2.70/1.58  #SimpNegUnit  : 18
% 2.70/1.58  #BackRed      : 1
% 2.70/1.58  
% 2.70/1.58  #Partial instantiations: 0
% 2.70/1.58  #Strategies tried      : 1
% 2.70/1.58  
% 2.70/1.58  Timing (in seconds)
% 2.70/1.58  ----------------------
% 2.70/1.58  Preprocessing        : 0.43
% 2.70/1.58  Parsing              : 0.25
% 2.70/1.58  CNF conversion       : 0.03
% 2.70/1.58  Main loop            : 0.26
% 2.70/1.58  Inferencing          : 0.10
% 2.70/1.58  Reduction            : 0.08
% 2.70/1.59  Demodulation         : 0.05
% 2.70/1.59  BG Simplification    : 0.02
% 2.70/1.59  Subsumption          : 0.04
% 2.70/1.59  Abstraction          : 0.02
% 2.70/1.59  MUC search           : 0.00
% 2.70/1.59  Cooper               : 0.00
% 2.70/1.59  Total                : 0.73
% 2.70/1.59  Index Insertion      : 0.00
% 2.70/1.59  Index Deletion       : 0.00
% 2.70/1.59  Index Matching       : 0.00
% 2.70/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
