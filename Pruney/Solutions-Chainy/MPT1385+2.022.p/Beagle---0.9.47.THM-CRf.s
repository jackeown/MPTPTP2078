%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:18 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 239 expanded)
%              Number of leaves         :   30 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  188 ( 701 expanded)
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

tff(f_107,negated_conjecture,(
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

tff(f_75,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_89,axiom,(
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

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_49,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_142,plain,(
    ! [B_55,A_56,C_57] :
      ( r2_hidden(B_55,k1_tops_1(A_56,C_57))
      | ~ m1_connsp_2(C_57,A_56,B_55)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_55,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    ! [B_55] :
      ( r2_hidden(B_55,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_55)
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_142])).

tff(c_151,plain,(
    ! [B_55] :
      ( r2_hidden(B_55,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_55)
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_147])).

tff(c_152,plain,(
    ! [B_55] :
      ( r2_hidden(B_55,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_55)
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_151])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_65,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_65,c_12])).

tff(c_73,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_70])).

tff(c_76,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_82,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_tarski(A_3),k1_zfmisc_1(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [C_43,A_44,B_45] :
      ( m2_connsp_2(C_43,A_44,B_45)
      | ~ r1_tarski(B_45,k1_tops_1(A_44,C_43))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_169,plain,(
    ! [C_62,A_63,A_64] :
      ( m2_connsp_2(C_62,A_63,k1_tarski(A_64))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(k1_tarski(A_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | ~ r2_hidden(A_64,k1_tops_1(A_63,C_62)) ) ),
    inference(resolution,[status(thm)],[c_4,c_100])).

tff(c_174,plain,(
    ! [A_64] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_64))
      | ~ m1_subset_1(k1_tarski(A_64),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(A_64,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_169])).

tff(c_179,plain,(
    ! [A_65] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_65))
      | ~ m1_subset_1(k1_tarski(A_65),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_65,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_174])).

tff(c_185,plain,(
    ! [A_66] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_66))
      | ~ r2_hidden(A_66,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_66,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_81,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_34,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_34])).

tff(c_85,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_84])).

tff(c_193,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_185,c_85])).

tff(c_194,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_197,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_200,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_200])).

tff(c_203,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_207,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_152,c_203])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_49,c_207])).

tff(c_216,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_219,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_231,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_219])).

tff(c_232,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_237,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_232,c_12])).

tff(c_240,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_237])).

tff(c_243,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_240])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_243])).

tff(c_249,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_248,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_215,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_250,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_215])).

tff(c_267,plain,(
    ! [B_75,A_76,C_77] :
      ( r1_tarski(B_75,k1_tops_1(A_76,C_77))
      | ~ m2_connsp_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_272,plain,(
    ! [B_75] :
      ( r1_tarski(B_75,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_267])).

tff(c_277,plain,(
    ! [B_78] :
      ( r1_tarski(B_78,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_272])).

tff(c_288,plain,(
    ! [A_79] :
      ( r1_tarski(k1_tarski(A_79),k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_79))
      | ~ r2_hidden(A_79,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | ~ r1_tarski(k1_tarski(A_1),B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_293,plain,(
    ! [A_80] :
      ( r2_hidden(A_80,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_80))
      | ~ r2_hidden(A_80,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_288,c_2])).

tff(c_297,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_250,c_293])).

tff(c_308,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_311,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_308])).

tff(c_314,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_311])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_314])).

tff(c_317,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_319,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_connsp_2(C_84,A_85,B_86)
      | ~ r2_hidden(B_86,k1_tops_1(A_85,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_317,c_319])).

tff(c_327,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_321])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_216,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.34  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.38/1.34  
% 2.38/1.34  %Foreground sorts:
% 2.38/1.34  
% 2.38/1.34  
% 2.38/1.34  %Background operators:
% 2.38/1.34  
% 2.38/1.34  
% 2.38/1.34  %Foreground operators:
% 2.38/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.34  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.38/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.38/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.38/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.38/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.38/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.38/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.34  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.38/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.34  
% 2.38/1.36  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 2.38/1.36  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.38/1.36  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.38/1.36  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.38/1.36  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.38/1.36  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.38/1.36  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.38/1.36  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.38/1.36  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.38/1.36  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.38/1.36  tff(c_26, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.38/1.36  tff(c_40, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.38/1.36  tff(c_49, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.38/1.36  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.38/1.36  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.38/1.36  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.38/1.36  tff(c_142, plain, (![B_55, A_56, C_57]: (r2_hidden(B_55, k1_tops_1(A_56, C_57)) | ~m1_connsp_2(C_57, A_56, B_55) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_55, u1_struct_0(A_56)) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.38/1.36  tff(c_147, plain, (![B_55]: (r2_hidden(B_55, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_55) | ~m1_subset_1(B_55, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_142])).
% 2.38/1.36  tff(c_151, plain, (![B_55]: (r2_hidden(B_55, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_55) | ~m1_subset_1(B_55, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_147])).
% 2.38/1.36  tff(c_152, plain, (![B_55]: (r2_hidden(B_55, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_55) | ~m1_subset_1(B_55, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_151])).
% 2.38/1.36  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.36  tff(c_52, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.36  tff(c_64, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_52])).
% 2.38/1.36  tff(c_65, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_64])).
% 2.38/1.36  tff(c_12, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.36  tff(c_70, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_65, c_12])).
% 2.38/1.36  tff(c_73, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_70])).
% 2.38/1.36  tff(c_76, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_73])).
% 2.38/1.36  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 2.38/1.36  tff(c_82, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_64])).
% 2.38/1.36  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.36  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k1_tarski(A_3), k1_zfmisc_1(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.36  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.36  tff(c_100, plain, (![C_43, A_44, B_45]: (m2_connsp_2(C_43, A_44, B_45) | ~r1_tarski(B_45, k1_tops_1(A_44, C_43)) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.38/1.36  tff(c_169, plain, (![C_62, A_63, A_64]: (m2_connsp_2(C_62, A_63, k1_tarski(A_64)) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(k1_tarski(A_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | ~r2_hidden(A_64, k1_tops_1(A_63, C_62)))), inference(resolution, [status(thm)], [c_4, c_100])).
% 2.38/1.36  tff(c_174, plain, (![A_64]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_64)) | ~m1_subset_1(k1_tarski(A_64), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(A_64, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_24, c_169])).
% 2.38/1.36  tff(c_179, plain, (![A_65]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_65)) | ~m1_subset_1(k1_tarski(A_65), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_65, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_174])).
% 2.38/1.36  tff(c_185, plain, (![A_66]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_66)) | ~r2_hidden(A_66, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_66, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_179])).
% 2.38/1.36  tff(c_81, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 2.38/1.36  tff(c_34, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.38/1.36  tff(c_84, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_34])).
% 2.38/1.36  tff(c_85, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_84])).
% 2.38/1.36  tff(c_193, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_185, c_85])).
% 2.38/1.36  tff(c_194, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_193])).
% 2.38/1.36  tff(c_197, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_194])).
% 2.38/1.36  tff(c_200, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_197])).
% 2.38/1.36  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_200])).
% 2.38/1.36  tff(c_203, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_193])).
% 2.38/1.36  tff(c_207, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_152, c_203])).
% 2.38/1.36  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_49, c_207])).
% 2.38/1.36  tff(c_216, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.38/1.36  tff(c_219, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.36  tff(c_231, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_219])).
% 2.38/1.36  tff(c_232, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_231])).
% 2.38/1.36  tff(c_237, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_232, c_12])).
% 2.38/1.36  tff(c_240, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_237])).
% 2.38/1.36  tff(c_243, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_240])).
% 2.38/1.36  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_243])).
% 2.38/1.36  tff(c_249, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_231])).
% 2.38/1.36  tff(c_248, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_231])).
% 2.38/1.36  tff(c_215, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 2.38/1.36  tff(c_250, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_215])).
% 2.38/1.36  tff(c_267, plain, (![B_75, A_76, C_77]: (r1_tarski(B_75, k1_tops_1(A_76, C_77)) | ~m2_connsp_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.38/1.36  tff(c_272, plain, (![B_75]: (r1_tarski(B_75, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_267])).
% 2.38/1.36  tff(c_277, plain, (![B_78]: (r1_tarski(B_78, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_272])).
% 2.38/1.36  tff(c_288, plain, (![A_79]: (r1_tarski(k1_tarski(A_79), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_79)) | ~r2_hidden(A_79, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_277])).
% 2.38/1.36  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | ~r1_tarski(k1_tarski(A_1), B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.36  tff(c_293, plain, (![A_80]: (r2_hidden(A_80, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_80)) | ~r2_hidden(A_80, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_288, c_2])).
% 2.38/1.36  tff(c_297, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_250, c_293])).
% 2.38/1.36  tff(c_308, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_297])).
% 2.38/1.36  tff(c_311, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_308])).
% 2.38/1.36  tff(c_314, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_311])).
% 2.38/1.36  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_314])).
% 2.38/1.36  tff(c_317, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_297])).
% 2.38/1.36  tff(c_319, plain, (![C_84, A_85, B_86]: (m1_connsp_2(C_84, A_85, B_86) | ~r2_hidden(B_86, k1_tops_1(A_85, C_84)) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.38/1.36  tff(c_321, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_317, c_319])).
% 2.38/1.36  tff(c_327, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_321])).
% 2.38/1.36  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_216, c_327])).
% 2.38/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.36  
% 2.38/1.36  Inference rules
% 2.38/1.36  ----------------------
% 2.38/1.36  #Ref     : 0
% 2.38/1.36  #Sup     : 51
% 2.38/1.36  #Fact    : 0
% 2.38/1.36  #Define  : 0
% 2.38/1.36  #Split   : 9
% 2.38/1.36  #Chain   : 0
% 2.38/1.36  #Close   : 0
% 2.38/1.36  
% 2.38/1.36  Ordering : KBO
% 2.38/1.36  
% 2.38/1.36  Simplification rules
% 2.38/1.36  ----------------------
% 2.38/1.36  #Subsume      : 2
% 2.38/1.36  #Demod        : 34
% 2.38/1.36  #Tautology    : 16
% 2.38/1.36  #SimpNegUnit  : 7
% 2.38/1.36  #BackRed      : 2
% 2.38/1.36  
% 2.38/1.36  #Partial instantiations: 0
% 2.38/1.36  #Strategies tried      : 1
% 2.38/1.36  
% 2.38/1.36  Timing (in seconds)
% 2.38/1.36  ----------------------
% 2.38/1.36  Preprocessing        : 0.32
% 2.38/1.36  Parsing              : 0.17
% 2.38/1.36  CNF conversion       : 0.02
% 2.38/1.36  Main loop            : 0.23
% 2.38/1.36  Inferencing          : 0.09
% 2.38/1.36  Reduction            : 0.06
% 2.38/1.36  Demodulation         : 0.04
% 2.38/1.36  BG Simplification    : 0.01
% 2.38/1.36  Subsumption          : 0.03
% 2.38/1.36  Abstraction          : 0.01
% 2.38/1.36  MUC search           : 0.00
% 2.38/1.36  Cooper               : 0.00
% 2.38/1.36  Total                : 0.58
% 2.38/1.36  Index Insertion      : 0.00
% 2.38/1.36  Index Deletion       : 0.00
% 2.38/1.36  Index Matching       : 0.00
% 2.38/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
