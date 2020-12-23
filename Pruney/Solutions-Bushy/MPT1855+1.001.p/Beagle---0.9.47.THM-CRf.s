%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1855+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  126 (1543 expanded)
%              Number of leaves         :   35 ( 515 expanded)
%              Depth                    :   24
%              Number of atoms          :  276 (5410 expanded)
%              Number of equality atoms :   38 ( 404 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_163,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_36,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ( v7_struct_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & u1_struct_0(A) = k6_domain_1(u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
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

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_69,plain,(
    ! [B_62,A_63] :
      ( l1_pre_topc(B_62)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_75,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    v7_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),u1_struct_0(A_1))
      | ~ v7_struct_0(A_1)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_108,plain,(
    ! [B_77,A_78] :
      ( m1_subset_1(u1_struct_0(B_77),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [A_32,C_34,B_33] :
      ( m1_subset_1(A_32,C_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_167,plain,(
    ! [A_97,A_98,B_99] :
      ( m1_subset_1(A_97,u1_struct_0(A_98))
      | ~ r2_hidden(A_97,u1_struct_0(B_99))
      | ~ m1_pre_topc(B_99,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_108,c_40])).

tff(c_188,plain,(
    ! [A_108,A_109,B_110] :
      ( m1_subset_1(A_108,u1_struct_0(A_109))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109)
      | v1_xboole_0(u1_struct_0(B_110))
      | ~ m1_subset_1(A_108,u1_struct_0(B_110)) ) ),
    inference(resolution,[status(thm)],[c_30,c_167])).

tff(c_192,plain,(
    ! [A_108] :
      ( m1_subset_1(A_108,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_108,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_188])).

tff(c_196,plain,(
    ! [A_108] :
      ( m1_subset_1(A_108,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_108,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_192])).

tff(c_197,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_22,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_215,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_197,c_22])).

tff(c_218,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_215])).

tff(c_221,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_218])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_221])).

tff(c_228,plain,(
    ! [A_112] :
      ( m1_subset_1(A_112,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( ~ v2_struct_0(k1_tex_2(A_12,B_13))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_236,plain,(
    ! [A_112] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',A_112))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_228,c_16])).

tff(c_252,plain,(
    ! [A_112] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',A_112))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_236])).

tff(c_259,plain,(
    ! [A_113] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',A_113))
      | ~ m1_subset_1(A_113,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_252])).

tff(c_263,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_266,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_263])).

tff(c_267,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_266])).

tff(c_271,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_274,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_271])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_274])).

tff(c_280,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_226,plain,(
    ! [A_108] :
      ( m1_subset_1(A_108,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_108,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_258,plain,(
    ! [A_112] :
      ( k6_domain_1(u1_struct_0('#skF_2'),A_112) = k1_tarski(A_112)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_228,c_26])).

tff(c_325,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_328,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_325,c_22])).

tff(c_331,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_328])).

tff(c_334,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_331])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_334])).

tff(c_351,plain,(
    ! [A_121] :
      ( k6_domain_1(u1_struct_0('#skF_2'),A_121) = k1_tarski(A_121)
      | ~ m1_subset_1(A_121,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_355,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_351])).

tff(c_358,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_50,c_355])).

tff(c_359,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_358])).

tff(c_279,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_pre_topc(k1_tex_2(A_12,B_13))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_239,plain,(
    ! [A_112] :
      ( v1_pre_topc(k1_tex_2('#skF_2',A_112))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_228,c_14])).

tff(c_256,plain,(
    ! [A_112] :
      ( v1_pre_topc(k1_tex_2('#skF_2',A_112))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_239])).

tff(c_281,plain,(
    ! [A_117] :
      ( v1_pre_topc(k1_tex_2('#skF_2',A_117))
      | ~ m1_subset_1(A_117,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_256])).

tff(c_285,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_281])).

tff(c_288,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_50,c_285])).

tff(c_289,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_288])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_pre_topc(k1_tex_2(A_12,B_13),A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_233,plain,(
    ! [A_112] :
      ( m1_pre_topc(k1_tex_2('#skF_2',A_112),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_228,c_12])).

tff(c_248,plain,(
    ! [A_112] :
      ( m1_pre_topc(k1_tex_2('#skF_2',A_112),'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_112,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_233])).

tff(c_290,plain,(
    ! [A_118] :
      ( m1_pre_topc(k1_tex_2('#skF_2',A_118),'#skF_2')
      | ~ m1_subset_1(A_118,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_248])).

tff(c_294,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_290])).

tff(c_297,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_50,c_294])).

tff(c_298,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_297])).

tff(c_315,plain,(
    ! [A_119,B_120] :
      ( k6_domain_1(u1_struct_0(A_119),B_120) = u1_struct_0(k1_tex_2(A_119,B_120))
      | ~ m1_pre_topc(k1_tex_2(A_119,B_120),A_119)
      | ~ v1_pre_topc(k1_tex_2(A_119,B_120))
      | v2_struct_0(k1_tex_2(A_119,B_120))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_317,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_315])).

tff(c_322,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_289,c_317])).

tff(c_323,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_279,c_322])).

tff(c_396,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) = k1_tarski('#skF_1'('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_323])).

tff(c_397,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_401,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_226,c_397])).

tff(c_404,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_401])).

tff(c_407,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_50,c_404])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_407])).

tff(c_411,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_410,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) = k1_tarski('#skF_1'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_46,plain,(
    ! [C_48] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2',C_48)),u1_pre_topc(k1_tex_2('#skF_2',C_48))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(C_48,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_489,plain,
    ( g1_pre_topc(k1_tarski('#skF_1'('#skF_3')),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_46])).

tff(c_520,plain,(
    g1_pre_topc(k1_tarski('#skF_1'('#skF_3')),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_489])).

tff(c_178,plain,(
    ! [C_104,B_105,A_106] :
      ( g1_pre_topc(u1_struct_0(C_104),u1_pre_topc(C_104)) = g1_pre_topc(u1_struct_0(B_105),u1_pre_topc(B_105))
      | u1_struct_0(C_104) != u1_struct_0(B_105)
      | ~ m1_pre_topc(C_104,A_106)
      | ~ m1_pre_topc(B_105,A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_182,plain,(
    ! [B_105] :
      ( g1_pre_topc(u1_struct_0(B_105),u1_pre_topc(B_105)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_105) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_105,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_178])).

tff(c_586,plain,(
    ! [B_130] :
      ( g1_pre_topc(u1_struct_0(B_130),u1_pre_topc(B_130)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_130) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_130,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_182])).

tff(c_600,plain,
    ( g1_pre_topc(k1_tarski('#skF_1'('#skF_3')),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
    | u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_586])).

tff(c_605,plain,
    ( g1_pre_topc(k1_tarski('#skF_1'('#skF_3')),u1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
    | k1_tarski('#skF_1'('#skF_3')) != u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_410,c_600])).

tff(c_606,plain,(
    k1_tarski('#skF_1'('#skF_3')) != u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_605])).

tff(c_103,plain,(
    ! [A_76] :
      ( m1_subset_1('#skF_1'(A_76),u1_struct_0(A_76))
      | ~ v7_struct_0(A_76)
      | ~ l1_struct_0(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_369,plain,(
    ! [A_122] :
      ( k6_domain_1(u1_struct_0(A_122),'#skF_1'(A_122)) = k1_tarski('#skF_1'(A_122))
      | v1_xboole_0(u1_struct_0(A_122))
      | ~ v7_struct_0(A_122)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_103,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( k6_domain_1(u1_struct_0(A_1),'#skF_1'(A_1)) = u1_struct_0(A_1)
      | ~ v7_struct_0(A_1)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_898,plain,(
    ! [A_156] :
      ( k1_tarski('#skF_1'(A_156)) = u1_struct_0(A_156)
      | ~ v7_struct_0(A_156)
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0(u1_struct_0(A_156))
      | ~ v7_struct_0(A_156)
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_4])).

tff(c_227,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_904,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_898,c_227])).

tff(c_917,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_50,c_904])).

tff(c_919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_606,c_917])).

%------------------------------------------------------------------------------
