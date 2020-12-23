%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1855+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:33 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 776 expanded)
%              Number of leaves         :   34 ( 267 expanded)
%              Depth                    :   23
%              Number of atoms          :  306 (2684 expanded)
%              Number of equality atoms :   43 ( 221 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & m1_pre_topc(B,A) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A,C)),u1_pre_topc(k1_tex_2(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ( v7_struct_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & u1_struct_0(A) = k6_domain_1(u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_51])).

tff(c_20,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    v7_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),u1_struct_0(A_2))
      | ~ v7_struct_0(A_2)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_77,plain,(
    ! [B_56,A_57] :
      ( m1_subset_1(u1_struct_0(B_56),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ! [A_27,C_29,B_28] :
      ( m1_subset_1(A_27,C_29)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(C_29))
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_116,plain,(
    ! [A_68,A_69,B_70] :
      ( m1_subset_1(A_68,u1_struct_0(A_69))
      | ~ r2_hidden(A_68,u1_struct_0(B_70))
      | ~ m1_pre_topc(B_70,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_77,c_32])).

tff(c_132,plain,(
    ! [A_75,A_76,B_77] :
      ( m1_subset_1(A_75,u1_struct_0(A_76))
      | ~ m1_pre_topc(B_77,A_76)
      | ~ l1_pre_topc(A_76)
      | v1_xboole_0(u1_struct_0(B_77))
      | ~ m1_subset_1(A_75,u1_struct_0(B_77)) ) ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_136,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_140,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_75,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_136])).

tff(c_141,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_24,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_144,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_24])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_144])).

tff(c_150,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_150])).

tff(c_157,plain,(
    ! [A_78] :
      ( m1_subset_1(A_78,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( ~ v2_struct_0(k1_tex_2(A_13,B_14))
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_165,plain,(
    ! [A_78] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',A_78))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_157,c_18])).

tff(c_181,plain,(
    ! [A_78] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',A_78))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_165])).

tff(c_188,plain,(
    ! [A_79] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',A_79))
      | ~ m1_subset_1(A_79,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_181])).

tff(c_192,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_188])).

tff(c_195,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_192])).

tff(c_196,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_195])).

tff(c_197,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_209,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_197])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_209])).

tff(c_214,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_215,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_155,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_75,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k6_domain_1(A_23,B_24) = k1_tarski(B_24)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_187,plain,(
    ! [A_78] :
      ( k6_domain_1(u1_struct_0('#skF_2'),A_78) = k1_tarski(A_78)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_157,c_28])).

tff(c_245,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_262,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_245,c_24])).

tff(c_265,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_262])).

tff(c_268,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_265])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_268])).

tff(c_285,plain,(
    ! [A_88] :
      ( k6_domain_1(u1_struct_0('#skF_2'),A_88) = k1_tarski(A_88)
      | ~ m1_subset_1(A_88,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_289,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_285])).

tff(c_292,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_40,c_289])).

tff(c_293,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_292])).

tff(c_392,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_tex_2(A_97,B_98) = C_99
      | u1_struct_0(C_99) != k6_domain_1(u1_struct_0(A_97),B_98)
      | ~ m1_pre_topc(C_99,A_97)
      | ~ v1_pre_topc(C_99)
      | v2_struct_0(C_99)
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_396,plain,(
    ! [C_99] :
      ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = C_99
      | u1_struct_0(C_99) != k1_tarski('#skF_1'('#skF_3'))
      | ~ m1_pre_topc(C_99,'#skF_2')
      | ~ v1_pre_topc(C_99)
      | v2_struct_0(C_99)
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_392])).

tff(c_400,plain,(
    ! [C_99] :
      ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = C_99
      | u1_struct_0(C_99) != k1_tarski('#skF_1'('#skF_3'))
      | ~ m1_pre_topc(C_99,'#skF_2')
      | ~ v1_pre_topc(C_99)
      | v2_struct_0(C_99)
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_396])).

tff(c_401,plain,(
    ! [C_99] :
      ( k1_tex_2('#skF_2','#skF_1'('#skF_3')) = C_99
      | u1_struct_0(C_99) != k1_tarski('#skF_1'('#skF_3'))
      | ~ m1_pre_topc(C_99,'#skF_2')
      | ~ v1_pre_topc(C_99)
      | v2_struct_0(C_99)
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_400])).

tff(c_403,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_407,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_155,c_403])).

tff(c_410,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_407])).

tff(c_413,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_40,c_410])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_413])).

tff(c_417,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_pre_topc(k1_tex_2(A_13,B_14))
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_168,plain,(
    ! [A_78] :
      ( v1_pre_topc(k1_tex_2('#skF_2',A_78))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_157,c_16])).

tff(c_185,plain,(
    ! [A_78] :
      ( v1_pre_topc(k1_tex_2('#skF_2',A_78))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_168])).

tff(c_216,plain,(
    ! [A_83] :
      ( v1_pre_topc(k1_tex_2('#skF_2',A_83))
      | ~ m1_subset_1(A_83,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_185])).

tff(c_220,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_216])).

tff(c_223,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_40,c_220])).

tff(c_224,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_223])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_pre_topc(k1_tex_2(A_13,B_14),A_13)
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_162,plain,(
    ! [A_78] :
      ( m1_pre_topc(k1_tex_2('#skF_2',A_78),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_157,c_14])).

tff(c_177,plain,(
    ! [A_78] :
      ( m1_pre_topc(k1_tex_2('#skF_2',A_78),'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_78,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_162])).

tff(c_225,plain,(
    ! [A_84] :
      ( m1_pre_topc(k1_tex_2('#skF_2',A_84),'#skF_2')
      | ~ m1_subset_1(A_84,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_177])).

tff(c_229,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_232,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_40,c_229])).

tff(c_233,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_232])).

tff(c_475,plain,(
    ! [A_101,B_102] :
      ( k6_domain_1(u1_struct_0(A_101),B_102) = u1_struct_0(k1_tex_2(A_101,B_102))
      | ~ m1_pre_topc(k1_tex_2(A_101,B_102),A_101)
      | ~ v1_pre_topc(k1_tex_2(A_101,B_102))
      | v2_struct_0(k1_tex_2(A_101,B_102))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_477,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_233,c_475])).

tff(c_482,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) = k1_tarski('#skF_1'('#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_417,c_224,c_293,c_477])).

tff(c_483,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) = k1_tarski('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_214,c_482])).

tff(c_299,plain,(
    ! [C_89,B_90,A_91] :
      ( g1_pre_topc(u1_struct_0(C_89),u1_pre_topc(C_89)) = g1_pre_topc(u1_struct_0(B_90),u1_pre_topc(B_90))
      | u1_struct_0(C_89) != u1_struct_0(B_90)
      | ~ m1_pre_topc(C_89,A_91)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_305,plain,(
    ! [B_90] :
      ( g1_pre_topc(u1_struct_0(B_90),u1_pre_topc(B_90)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_90) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_90,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_299])).

tff(c_337,plain,(
    ! [B_94] :
      ( g1_pre_topc(u1_struct_0(B_94),u1_pre_topc(B_94)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_94) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_94,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_305])).

tff(c_36,plain,(
    ! [C_41] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2',C_41)),u1_pre_topc(k1_tex_2('#skF_2',C_41))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_370,plain,(
    ! [C_95] :
      ( ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | u1_struct_0(k1_tex_2('#skF_2',C_95)) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(k1_tex_2('#skF_2',C_95),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_36])).

tff(c_383,plain,(
    ! [A_96] :
      ( u1_struct_0(k1_tex_2('#skF_2',A_96)) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(k1_tex_2('#skF_2',A_96),'#skF_2')
      | ~ m1_subset_1(A_96,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_155,c_370])).

tff(c_387,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_383])).

tff(c_390,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) != u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_40,c_233,c_387])).

tff(c_391,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) != u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_390])).

tff(c_485,plain,(
    k1_tarski('#skF_1'('#skF_3')) != u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_391])).

tff(c_72,plain,(
    ! [A_55] :
      ( m1_subset_1('#skF_1'(A_55),u1_struct_0(A_55))
      | ~ v7_struct_0(A_55)
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_322,plain,(
    ! [A_93] :
      ( k6_domain_1(u1_struct_0(A_93),'#skF_1'(A_93)) = k1_tarski('#skF_1'(A_93))
      | v1_xboole_0(u1_struct_0(A_93))
      | ~ v7_struct_0(A_93)
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_72,c_28])).

tff(c_6,plain,(
    ! [A_2] :
      ( k6_domain_1(u1_struct_0(A_2),'#skF_1'(A_2)) = u1_struct_0(A_2)
      | ~ v7_struct_0(A_2)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_734,plain,(
    ! [A_123] :
      ( k1_tarski('#skF_1'(A_123)) = u1_struct_0(A_123)
      | ~ v7_struct_0(A_123)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123)
      | v1_xboole_0(u1_struct_0(A_123))
      | ~ v7_struct_0(A_123)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_6])).

tff(c_156,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_740,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_734,c_156])).

tff(c_753,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_40,c_740])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_485,c_753])).

%------------------------------------------------------------------------------
