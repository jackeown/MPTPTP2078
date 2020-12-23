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
% DateTime   : Thu Dec  3 10:29:40 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 165 expanded)
%              Number of leaves         :   33 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 ( 425 expanded)
%              Number of equality atoms :   22 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_74,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k1_tarski(A_46),k1_zfmisc_1(B_47))
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tarski(A_46),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_74,c_16])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_224,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_233,plain,(
    ! [B_75] : k9_subset_1(u1_struct_0('#skF_3'),B_75,'#skF_4') = k3_xboole_0(B_75,'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_224])).

tff(c_293,plain,(
    ! [A_89,C_90,B_91] :
      ( k9_subset_1(A_89,C_90,B_91) = k9_subset_1(A_89,B_91,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_299,plain,(
    ! [B_91] : k9_subset_1(u1_struct_0('#skF_3'),B_91,'#skF_4') = k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_91) ),
    inference(resolution,[status(thm)],[c_40,c_293])).

tff(c_303,plain,(
    ! [B_91] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_91) = k3_xboole_0(B_91,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_299])).

tff(c_113,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_122,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_113])).

tff(c_123,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_124,plain,(
    ! [A_60,B_61] :
      ( k6_domain_1(A_60,B_61) = k1_tarski(B_61)
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_136,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_142,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_136])).

tff(c_32,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_143,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_142,c_32])).

tff(c_313,plain,(
    k3_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),'#skF_4') != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_143])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_57,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_80,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_355,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(A_100,B_102)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_917,plain,(
    ! [A_144,B_145,B_146,B_147] :
      ( r2_hidden('#skF_1'(A_144,B_145),B_146)
      | ~ r1_tarski(B_147,B_146)
      | ~ r1_tarski(A_144,B_147)
      | r1_tarski(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_355,c_2])).

tff(c_930,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_1'(A_148,B_149),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_148,'#skF_4')
      | r1_tarski(A_148,B_149) ) ),
    inference(resolution,[status(thm)],[c_65,c_917])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_954,plain,(
    ! [A_148] :
      ( ~ r1_tarski(A_148,'#skF_4')
      | r1_tarski(A_148,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_930,c_4])).

tff(c_1838,plain,(
    ! [A_172,B_173,B_174,A_175] :
      ( r2_hidden('#skF_1'(A_172,B_173),B_174)
      | ~ r1_tarski(A_172,k1_tarski(A_175))
      | r1_tarski(A_172,B_173)
      | ~ r2_hidden(A_175,B_174) ) ),
    inference(resolution,[status(thm)],[c_78,c_917])).

tff(c_1855,plain,(
    ! [A_176,B_177,B_178] :
      ( r2_hidden('#skF_1'(k1_tarski(A_176),B_177),B_178)
      | r1_tarski(k1_tarski(A_176),B_177)
      | ~ r2_hidden(A_176,B_178) ) ),
    inference(resolution,[status(thm)],[c_72,c_1838])).

tff(c_2295,plain,(
    ! [A_210,B_211,B_212,B_213] :
      ( r2_hidden('#skF_1'(k1_tarski(A_210),B_211),B_212)
      | ~ r1_tarski(B_213,B_212)
      | r1_tarski(k1_tarski(A_210),B_211)
      | ~ r2_hidden(A_210,B_213) ) ),
    inference(resolution,[status(thm)],[c_1855,c_2])).

tff(c_4580,plain,(
    ! [A_277,B_278,A_279] :
      ( r2_hidden('#skF_1'(k1_tarski(A_277),B_278),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tarski(A_277),B_278)
      | ~ r2_hidden(A_277,A_279)
      | ~ r1_tarski(A_279,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_954,c_2295])).

tff(c_4604,plain,(
    ! [B_278] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_5'),B_278),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tarski('#skF_5'),B_278)
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_4580])).

tff(c_4621,plain,(
    ! [B_280] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_5'),B_280),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tarski('#skF_5'),B_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4604])).

tff(c_4651,plain,(
    r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4621,c_4])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_996,plain,(
    ! [A_151,B_152,C_153] :
      ( k9_subset_1(u1_struct_0(A_151),B_152,k2_pre_topc(A_151,C_153)) = C_153
      | ~ r1_tarski(C_153,B_152)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4892,plain,(
    ! [A_282,B_283,A_284] :
      ( k9_subset_1(u1_struct_0(A_282),B_283,k2_pre_topc(A_282,A_284)) = A_284
      | ~ r1_tarski(A_284,B_283)
      | ~ v2_tex_2(B_283,A_282)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282)
      | ~ r1_tarski(A_284,u1_struct_0(A_282)) ) ),
    inference(resolution,[status(thm)],[c_18,c_996])).

tff(c_4902,plain,(
    ! [A_284] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_284)) = A_284
      | ~ r1_tarski(A_284,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_284,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_40,c_4892])).

tff(c_4908,plain,(
    ! [A_284] :
      ( k3_xboole_0(k2_pre_topc('#skF_3',A_284),'#skF_4') = A_284
      | ~ r1_tarski(A_284,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_284,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_303,c_4902])).

tff(c_5210,plain,(
    ! [A_286] :
      ( k3_xboole_0(k2_pre_topc('#skF_3',A_286),'#skF_4') = A_286
      | ~ r1_tarski(A_286,'#skF_4')
      | ~ r1_tarski(A_286,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4908])).

tff(c_5213,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),'#skF_4') = k1_tarski('#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4651,c_5210])).

tff(c_5256,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_5213])).

tff(c_5282,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_5256])).

tff(c_5287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5282])).

tff(c_5288,plain,(
    ! [A_59] : ~ r2_hidden(A_59,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_5291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5288,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.13  
% 5.84/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.13  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.84/2.13  
% 5.84/2.13  %Foreground sorts:
% 5.84/2.13  
% 5.84/2.13  
% 5.84/2.13  %Background operators:
% 5.84/2.13  
% 5.84/2.13  
% 5.84/2.13  %Foreground operators:
% 5.84/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.84/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.84/2.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.84/2.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.84/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.84/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.84/2.13  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.84/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.84/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.84/2.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.84/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.84/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.84/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.84/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.84/2.13  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.84/2.13  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.84/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.84/2.13  
% 5.92/2.15  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 5.92/2.15  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 5.92/2.15  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.92/2.15  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.92/2.15  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 5.92/2.15  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.92/2.15  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.92/2.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.92/2.15  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 5.92/2.15  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_74, plain, (![A_46, B_47]: (m1_subset_1(k1_tarski(A_46), k1_zfmisc_1(B_47)) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.92/2.15  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.15  tff(c_78, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), B_47) | ~r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_74, c_16])).
% 5.92/2.15  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_224, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.92/2.15  tff(c_233, plain, (![B_75]: (k9_subset_1(u1_struct_0('#skF_3'), B_75, '#skF_4')=k3_xboole_0(B_75, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_224])).
% 5.92/2.15  tff(c_293, plain, (![A_89, C_90, B_91]: (k9_subset_1(A_89, C_90, B_91)=k9_subset_1(A_89, B_91, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.92/2.15  tff(c_299, plain, (![B_91]: (k9_subset_1(u1_struct_0('#skF_3'), B_91, '#skF_4')=k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_91))), inference(resolution, [status(thm)], [c_40, c_293])).
% 5.92/2.15  tff(c_303, plain, (![B_91]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_91)=k3_xboole_0(B_91, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_299])).
% 5.92/2.15  tff(c_113, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.92/2.15  tff(c_122, plain, (![A_59]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_59, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_113])).
% 5.92/2.15  tff(c_123, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_122])).
% 5.92/2.15  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_124, plain, (![A_60, B_61]: (k6_domain_1(A_60, B_61)=k1_tarski(B_61) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.15  tff(c_136, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_124])).
% 5.92/2.15  tff(c_142, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_123, c_136])).
% 5.92/2.15  tff(c_32, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_143, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_142, c_32])).
% 5.92/2.15  tff(c_313, plain, (k3_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), '#skF_4')!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_143])).
% 5.92/2.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.15  tff(c_67, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.15  tff(c_72, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_67])).
% 5.92/2.15  tff(c_57, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.15  tff(c_65, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_57])).
% 5.92/2.15  tff(c_80, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.15  tff(c_355, plain, (![A_100, B_101, B_102]: (r2_hidden('#skF_1'(A_100, B_101), B_102) | ~r1_tarski(A_100, B_102) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_6, c_80])).
% 5.92/2.15  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.15  tff(c_917, plain, (![A_144, B_145, B_146, B_147]: (r2_hidden('#skF_1'(A_144, B_145), B_146) | ~r1_tarski(B_147, B_146) | ~r1_tarski(A_144, B_147) | r1_tarski(A_144, B_145))), inference(resolution, [status(thm)], [c_355, c_2])).
% 5.92/2.15  tff(c_930, plain, (![A_148, B_149]: (r2_hidden('#skF_1'(A_148, B_149), u1_struct_0('#skF_3')) | ~r1_tarski(A_148, '#skF_4') | r1_tarski(A_148, B_149))), inference(resolution, [status(thm)], [c_65, c_917])).
% 5.92/2.15  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.15  tff(c_954, plain, (![A_148]: (~r1_tarski(A_148, '#skF_4') | r1_tarski(A_148, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_930, c_4])).
% 5.92/2.15  tff(c_1838, plain, (![A_172, B_173, B_174, A_175]: (r2_hidden('#skF_1'(A_172, B_173), B_174) | ~r1_tarski(A_172, k1_tarski(A_175)) | r1_tarski(A_172, B_173) | ~r2_hidden(A_175, B_174))), inference(resolution, [status(thm)], [c_78, c_917])).
% 5.92/2.15  tff(c_1855, plain, (![A_176, B_177, B_178]: (r2_hidden('#skF_1'(k1_tarski(A_176), B_177), B_178) | r1_tarski(k1_tarski(A_176), B_177) | ~r2_hidden(A_176, B_178))), inference(resolution, [status(thm)], [c_72, c_1838])).
% 5.92/2.15  tff(c_2295, plain, (![A_210, B_211, B_212, B_213]: (r2_hidden('#skF_1'(k1_tarski(A_210), B_211), B_212) | ~r1_tarski(B_213, B_212) | r1_tarski(k1_tarski(A_210), B_211) | ~r2_hidden(A_210, B_213))), inference(resolution, [status(thm)], [c_1855, c_2])).
% 5.92/2.15  tff(c_4580, plain, (![A_277, B_278, A_279]: (r2_hidden('#skF_1'(k1_tarski(A_277), B_278), u1_struct_0('#skF_3')) | r1_tarski(k1_tarski(A_277), B_278) | ~r2_hidden(A_277, A_279) | ~r1_tarski(A_279, '#skF_4'))), inference(resolution, [status(thm)], [c_954, c_2295])).
% 5.92/2.15  tff(c_4604, plain, (![B_278]: (r2_hidden('#skF_1'(k1_tarski('#skF_5'), B_278), u1_struct_0('#skF_3')) | r1_tarski(k1_tarski('#skF_5'), B_278) | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_4580])).
% 5.92/2.15  tff(c_4621, plain, (![B_280]: (r2_hidden('#skF_1'(k1_tarski('#skF_5'), B_280), u1_struct_0('#skF_3')) | r1_tarski(k1_tarski('#skF_5'), B_280))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4604])).
% 5.92/2.15  tff(c_4651, plain, (r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4621, c_4])).
% 5.92/2.15  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_38, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.15  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.15  tff(c_996, plain, (![A_151, B_152, C_153]: (k9_subset_1(u1_struct_0(A_151), B_152, k2_pre_topc(A_151, C_153))=C_153 | ~r1_tarski(C_153, B_152) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(A_151))) | ~v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.92/2.15  tff(c_4892, plain, (![A_282, B_283, A_284]: (k9_subset_1(u1_struct_0(A_282), B_283, k2_pre_topc(A_282, A_284))=A_284 | ~r1_tarski(A_284, B_283) | ~v2_tex_2(B_283, A_282) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282) | ~r1_tarski(A_284, u1_struct_0(A_282)))), inference(resolution, [status(thm)], [c_18, c_996])).
% 5.92/2.15  tff(c_4902, plain, (![A_284]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_284))=A_284 | ~r1_tarski(A_284, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_284, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_40, c_4892])).
% 5.92/2.15  tff(c_4908, plain, (![A_284]: (k3_xboole_0(k2_pre_topc('#skF_3', A_284), '#skF_4')=A_284 | ~r1_tarski(A_284, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_284, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_303, c_4902])).
% 5.92/2.15  tff(c_5210, plain, (![A_286]: (k3_xboole_0(k2_pre_topc('#skF_3', A_286), '#skF_4')=A_286 | ~r1_tarski(A_286, '#skF_4') | ~r1_tarski(A_286, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_4908])).
% 5.92/2.15  tff(c_5213, plain, (k3_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), '#skF_4')=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4651, c_5210])).
% 5.92/2.15  tff(c_5256, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_313, c_5213])).
% 5.92/2.15  tff(c_5282, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_5256])).
% 5.92/2.15  tff(c_5287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_5282])).
% 5.92/2.15  tff(c_5288, plain, (![A_59]: (~r2_hidden(A_59, '#skF_4'))), inference(splitRight, [status(thm)], [c_122])).
% 5.92/2.15  tff(c_5291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5288, c_34])).
% 5.92/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.15  
% 5.92/2.15  Inference rules
% 5.92/2.15  ----------------------
% 5.92/2.15  #Ref     : 0
% 5.92/2.15  #Sup     : 1261
% 5.92/2.15  #Fact    : 0
% 5.92/2.15  #Define  : 0
% 5.92/2.15  #Split   : 5
% 5.92/2.15  #Chain   : 0
% 5.92/2.15  #Close   : 0
% 5.92/2.15  
% 5.92/2.15  Ordering : KBO
% 5.92/2.15  
% 5.92/2.15  Simplification rules
% 5.92/2.15  ----------------------
% 5.92/2.15  #Subsume      : 356
% 5.92/2.15  #Demod        : 235
% 5.92/2.15  #Tautology    : 456
% 5.92/2.15  #SimpNegUnit  : 17
% 5.92/2.15  #BackRed      : 3
% 5.92/2.15  
% 5.92/2.15  #Partial instantiations: 0
% 5.92/2.15  #Strategies tried      : 1
% 5.92/2.15  
% 5.92/2.15  Timing (in seconds)
% 5.92/2.15  ----------------------
% 5.92/2.15  Preprocessing        : 0.34
% 5.92/2.15  Parsing              : 0.18
% 5.92/2.15  CNF conversion       : 0.02
% 5.92/2.15  Main loop            : 1.05
% 5.92/2.15  Inferencing          : 0.37
% 5.92/2.15  Reduction            : 0.32
% 5.92/2.15  Demodulation         : 0.22
% 5.92/2.15  BG Simplification    : 0.04
% 5.92/2.15  Subsumption          : 0.24
% 5.92/2.15  Abstraction          : 0.06
% 5.92/2.15  MUC search           : 0.00
% 5.92/2.15  Cooper               : 0.00
% 5.92/2.15  Total                : 1.43
% 5.92/2.15  Index Insertion      : 0.00
% 5.92/2.15  Index Deletion       : 0.00
% 5.92/2.15  Index Matching       : 0.00
% 5.92/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
