%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:04 EST 2020

% Result     : Theorem 5.38s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  183 (1452 expanded)
%              Number of leaves         :   43 ( 478 expanded)
%              Depth                    :   21
%              Number of atoms          :  386 (3937 expanded)
%              Number of equality atoms :   33 ( 307 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > o_2_0_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(o_2_0_pre_topc,type,(
    o_2_0_pre_topc: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_211,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_174,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_198,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(o_2_0_pre_topc(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_0_pre_topc)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_20,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_14,plain,(
    ! [A_8] : ~ v1_subset_1('#skF_1'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1('#skF_1'(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1656,plain,(
    ! [B_253,A_254] :
      ( v1_subset_1(B_253,A_254)
      | B_253 = A_254
      | ~ m1_subset_1(B_253,k1_zfmisc_1(A_254)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1666,plain,(
    ! [A_8] :
      ( v1_subset_1('#skF_1'(A_8),A_8)
      | '#skF_1'(A_8) = A_8 ) ),
    inference(resolution,[status(thm)],[c_16,c_1656])).

tff(c_1671,plain,(
    ! [A_8] : '#skF_1'(A_8) = A_8 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1666])).

tff(c_1674,plain,(
    ! [A_8] : ~ v1_subset_1(A_8,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_14])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_80,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_80])).

tff(c_89,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_tarski(A_3),k1_zfmisc_1(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1814,plain,(
    ! [A_278,B_279] :
      ( v1_subset_1(k1_tarski(A_278),B_279)
      | k1_tarski(A_278) = B_279
      | ~ r2_hidden(A_278,B_279) ) ),
    inference(resolution,[status(thm)],[c_10,c_1656])).

tff(c_1718,plain,(
    ! [A_264,B_265] :
      ( k6_domain_1(A_264,B_265) = k1_tarski(B_265)
      | ~ m1_subset_1(B_265,A_264)
      | v1_xboole_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1730,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_1718])).

tff(c_1736,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1730])).

tff(c_200,plain,(
    ! [A_86,B_87] :
      ( k6_domain_1(A_86,B_87) = k1_tarski(B_87)
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_212,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_200])).

tff(c_218,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_212])).

tff(c_76,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_90,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_219,plain,(
    v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_90])).

tff(c_299,plain,(
    ! [A_100,B_101] :
      ( ~ v1_zfmisc_1(A_100)
      | ~ v1_subset_1(k6_domain_1(A_100,B_101),A_100)
      | ~ m1_subset_1(B_101,A_100)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_308,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_299])).

tff(c_314,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_219,c_308])).

tff(c_315,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_314])).

tff(c_459,plain,(
    ! [A_128,B_129] :
      ( m1_pre_topc(k1_tex_2(A_128,B_129),A_128)
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_468,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_459])).

tff(c_474,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_468])).

tff(c_475,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_474])).

tff(c_778,plain,(
    ! [A_163,B_164] :
      ( m1_subset_1('#skF_2'(A_163,B_164),k1_zfmisc_1(u1_struct_0(A_163)))
      | v1_tex_2(B_164,A_163)
      | ~ m1_pre_topc(B_164,A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    ! [B_36,A_35] :
      ( v1_subset_1(B_36,A_35)
      | B_36 = A_35
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1553,plain,(
    ! [A_233,B_234] :
      ( v1_subset_1('#skF_2'(A_233,B_234),u1_struct_0(A_233))
      | u1_struct_0(A_233) = '#skF_2'(A_233,B_234)
      | v1_tex_2(B_234,A_233)
      | ~ m1_pre_topc(B_234,A_233)
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_778,c_40])).

tff(c_34,plain,(
    ! [A_25,B_31] :
      ( ~ v1_subset_1('#skF_2'(A_25,B_31),u1_struct_0(A_25))
      | v1_tex_2(B_31,A_25)
      | ~ m1_pre_topc(B_31,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1566,plain,(
    ! [A_235,B_236] :
      ( u1_struct_0(A_235) = '#skF_2'(A_235,B_236)
      | v1_tex_2(B_236,A_235)
      | ~ m1_pre_topc(B_236,A_235)
      | ~ l1_pre_topc(A_235) ) ),
    inference(resolution,[status(thm)],[c_1553,c_34])).

tff(c_70,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_122,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_70])).

tff(c_1573,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1566,c_122])).

tff(c_1577,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_475,c_1573])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( l1_pre_topc(B_16)
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_478,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_475,c_22])).

tff(c_481,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_478])).

tff(c_395,plain,(
    ! [A_113,B_114] :
      ( ~ v2_struct_0(k1_tex_2(A_113,B_114))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_405,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_395])).

tff(c_410,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_405])).

tff(c_411,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_410])).

tff(c_487,plain,(
    ! [B_131,A_132] :
      ( u1_struct_0(B_131) = '#skF_2'(A_132,B_131)
      | v1_tex_2(B_131,A_132)
      | ~ m1_pre_topc(B_131,A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_490,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_487,c_122])).

tff(c_493,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_475,c_490])).

tff(c_26,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_547,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_26])).

tff(c_590,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_547])).

tff(c_592,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_595,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_592])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_595])).

tff(c_600,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_601,plain,(
    l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_413,plain,(
    ! [A_116,B_117] :
      ( v7_struct_0(k1_tex_2(A_116,B_117))
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l1_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_423,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_413])).

tff(c_428,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_423])).

tff(c_429,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_428])).

tff(c_60,plain,(
    ! [A_47,B_49] :
      ( v1_subset_1(k6_domain_1(A_47,B_49),A_47)
      | ~ m1_subset_1(B_49,A_47)
      | v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_947,plain,(
    ! [A_179,B_180] :
      ( ~ v7_struct_0(A_179)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_179),B_180),u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_struct_0(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1191,plain,(
    ! [A_203,B_204] :
      ( ~ v7_struct_0(A_203)
      | ~ l1_struct_0(A_203)
      | v2_struct_0(A_203)
      | ~ m1_subset_1(B_204,u1_struct_0(A_203))
      | v1_zfmisc_1(u1_struct_0(A_203))
      | v1_xboole_0(u1_struct_0(A_203)) ) ),
    inference(resolution,[status(thm)],[c_60,c_947])).

tff(c_1197,plain,(
    ! [B_204] :
      ( ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_204,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_3','#skF_4')))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_3','#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_1191])).

tff(c_1213,plain,(
    ! [B_204] :
      ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_204,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_493,c_601,c_429,c_1197])).

tff(c_1214,plain,(
    ! [B_204] :
      ( ~ m1_subset_1(B_204,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_411,c_1213])).

tff(c_1222,plain,(
    ! [B_204] : ~ m1_subset_1(B_204,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1214])).

tff(c_138,plain,(
    ! [B_75,A_76] :
      ( v1_subset_1(B_75,A_76)
      | B_75 = A_76
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_148,plain,(
    ! [A_8] :
      ( v1_subset_1('#skF_1'(A_8),A_8)
      | '#skF_1'(A_8) = A_8 ) ),
    inference(resolution,[status(thm)],[c_16,c_138])).

tff(c_153,plain,(
    ! [A_8] : '#skF_1'(A_8) = A_8 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_148])).

tff(c_155,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_16])).

tff(c_364,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(o_2_0_pre_topc(A_108,B_109),B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_377,plain,(
    ! [A_108] :
      ( m1_subset_1(o_2_0_pre_topc(A_108,u1_struct_0(A_108)),u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_155,c_364])).

tff(c_533,plain,
    ( m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3','#skF_4'),u1_struct_0(k1_tex_2('#skF_3','#skF_4'))),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_377])).

tff(c_582,plain,(
    m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_493,c_533])).

tff(c_1224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1222,c_582])).

tff(c_1225,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1214])).

tff(c_1588,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1577,c_1225])).

tff(c_1606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_1588])).

tff(c_1607,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1610,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1607,c_70])).

tff(c_1737,plain,(
    ~ v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1736,c_1610])).

tff(c_1825,plain,
    ( u1_struct_0('#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1814,c_1737])).

tff(c_1845,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1825])).

tff(c_1848,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_1845])).

tff(c_1851,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1848])).

tff(c_1853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1851])).

tff(c_1854,plain,(
    u1_struct_0('#skF_3') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1825])).

tff(c_1859,plain,(
    m1_subset_1('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_64])).

tff(c_2232,plain,(
    ! [A_305,B_306] :
      ( m1_pre_topc(k1_tex_2(A_305,B_306),A_305)
      | ~ m1_subset_1(B_306,u1_struct_0(A_305))
      | ~ l1_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2238,plain,(
    ! [B_306] :
      ( m1_pre_topc(k1_tex_2('#skF_3',B_306),'#skF_3')
      | ~ m1_subset_1(B_306,k1_tarski('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_2232])).

tff(c_2245,plain,(
    ! [B_306] :
      ( m1_pre_topc(k1_tex_2('#skF_3',B_306),'#skF_3')
      | ~ m1_subset_1(B_306,k1_tarski('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2238])).

tff(c_2248,plain,(
    ! [B_307] :
      ( m1_pre_topc(k1_tex_2('#skF_3',B_307),'#skF_3')
      | ~ m1_subset_1(B_307,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2245])).

tff(c_2260,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1859,c_2248])).

tff(c_2264,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2260,c_22])).

tff(c_2267,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2264])).

tff(c_1796,plain,(
    ! [A_272,B_273] :
      ( ~ v2_struct_0(k1_tex_2(A_272,B_273))
      | ~ m1_subset_1(B_273,u1_struct_0(A_272))
      | ~ l1_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1803,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1796])).

tff(c_1807,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1803])).

tff(c_1808,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1807])).

tff(c_56,plain,(
    ! [B_43,A_41] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_pre_topc(B_43,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1869,plain,(
    ! [B_43] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(k1_tarski('#skF_4')))
      | ~ m1_pre_topc(B_43,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_56])).

tff(c_1945,plain,(
    ! [B_286] :
      ( m1_subset_1(u1_struct_0(B_286),k1_zfmisc_1(k1_tarski('#skF_4')))
      | ~ m1_pre_topc(B_286,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1869])).

tff(c_2563,plain,(
    ! [B_337] :
      ( v1_subset_1(u1_struct_0(B_337),k1_tarski('#skF_4'))
      | u1_struct_0(B_337) = k1_tarski('#skF_4')
      | ~ m1_pre_topc(B_337,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1945,c_40])).

tff(c_1858,plain,(
    ~ v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_89])).

tff(c_1857,plain,(
    k6_domain_1(k1_tarski('#skF_4'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_1736])).

tff(c_2040,plain,(
    ! [A_294,B_295] :
      ( v1_subset_1(k6_domain_1(A_294,B_295),A_294)
      | ~ m1_subset_1(B_295,A_294)
      | v1_zfmisc_1(A_294)
      | v1_xboole_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2048,plain,
    ( v1_subset_1(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_tarski('#skF_4'))
    | v1_zfmisc_1(k1_tarski('#skF_4'))
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1857,c_2040])).

tff(c_2058,plain,
    ( v1_subset_1(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | v1_zfmisc_1(k1_tarski('#skF_4'))
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1859,c_2048])).

tff(c_2059,plain,(
    v1_zfmisc_1(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1858,c_1674,c_2058])).

tff(c_1879,plain,(
    ! [B_43] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(k1_tarski('#skF_4')))
      | ~ m1_pre_topc(B_43,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1869])).

tff(c_2095,plain,(
    ! [B_299,A_300] :
      ( v1_xboole_0(B_299)
      | ~ v1_subset_1(B_299,A_300)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(A_300))
      | ~ v1_zfmisc_1(A_300)
      | v1_xboole_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2101,plain,(
    ! [B_43] :
      ( v1_xboole_0(u1_struct_0(B_43))
      | ~ v1_subset_1(u1_struct_0(B_43),k1_tarski('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski('#skF_4'))
      | v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_pre_topc(B_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1879,c_2095])).

tff(c_2120,plain,(
    ! [B_43] :
      ( v1_xboole_0(u1_struct_0(B_43))
      | ~ v1_subset_1(u1_struct_0(B_43),k1_tarski('#skF_4'))
      | v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_pre_topc(B_43,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2059,c_2101])).

tff(c_2121,plain,(
    ! [B_43] :
      ( v1_xboole_0(u1_struct_0(B_43))
      | ~ v1_subset_1(u1_struct_0(B_43),k1_tarski('#skF_4'))
      | ~ m1_pre_topc(B_43,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1858,c_2120])).

tff(c_2576,plain,(
    ! [B_338] :
      ( v1_xboole_0(u1_struct_0(B_338))
      | u1_struct_0(B_338) = k1_tarski('#skF_4')
      | ~ m1_pre_topc(B_338,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2563,c_2121])).

tff(c_2593,plain,(
    ! [B_339] :
      ( ~ l1_struct_0(B_339)
      | v2_struct_0(B_339)
      | u1_struct_0(B_339) = k1_tarski('#skF_4')
      | ~ m1_pre_topc(B_339,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2576,c_26])).

tff(c_2603,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_2260,c_2593])).

tff(c_2613,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1808,c_2603])).

tff(c_2614,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2613])).

tff(c_2617,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_2614])).

tff(c_2621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_2617])).

tff(c_2622,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2613])).

tff(c_2864,plain,(
    ! [B_342,A_343] :
      ( v1_subset_1(u1_struct_0(B_342),u1_struct_0(A_343))
      | ~ m1_subset_1(u1_struct_0(B_342),k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ v1_tex_2(B_342,A_343)
      | ~ m1_pre_topc(B_342,A_343)
      | ~ l1_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3466,plain,(
    ! [B_365,A_366] :
      ( v1_subset_1(u1_struct_0(B_365),u1_struct_0(A_366))
      | ~ v1_tex_2(B_365,A_366)
      | ~ m1_pre_topc(B_365,A_366)
      | ~ l1_pre_topc(A_366) ) ),
    inference(resolution,[status(thm)],[c_56,c_2864])).

tff(c_3493,plain,(
    ! [B_365] :
      ( v1_subset_1(u1_struct_0(B_365),k1_tarski('#skF_4'))
      | ~ v1_tex_2(B_365,'#skF_3')
      | ~ m1_pre_topc(B_365,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_3466])).

tff(c_3519,plain,(
    ! [B_369] :
      ( v1_subset_1(u1_struct_0(B_369),k1_tarski('#skF_4'))
      | ~ v1_tex_2(B_369,'#skF_3')
      | ~ m1_pre_topc(B_369,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3493])).

tff(c_3530,plain,
    ( v1_subset_1(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2622,c_3519])).

tff(c_3541,plain,(
    v1_subset_1(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2260,c_1607,c_3530])).

tff(c_3543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1674,c_3541])).

tff(c_3545,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_3550,plain,(
    ! [A_374] :
      ( ~ v1_xboole_0(u1_struct_0(A_374))
      | ~ l1_struct_0(A_374)
      | v2_struct_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3553,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3545,c_3550])).

tff(c_3556,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3553])).

tff(c_3569,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3556])).

tff(c_3573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.38/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/2.07  
% 5.38/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/2.07  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > o_2_0_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.38/2.07  
% 5.38/2.07  %Foreground sorts:
% 5.38/2.07  
% 5.38/2.07  
% 5.38/2.07  %Background operators:
% 5.38/2.07  
% 5.38/2.07  
% 5.38/2.07  %Foreground operators:
% 5.38/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.38/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.38/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.38/2.07  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.38/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.38/2.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.38/2.07  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 5.38/2.07  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.38/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.38/2.07  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.38/2.07  tff(o_2_0_pre_topc, type, o_2_0_pre_topc: ($i * $i) > $i).
% 5.38/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.38/2.07  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.38/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.38/2.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.38/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.38/2.07  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 5.38/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.38/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.38/2.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.38/2.07  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.38/2.07  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.38/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.38/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.38/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.38/2.07  
% 5.78/2.09  tff(f_211, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 5.78/2.09  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.78/2.09  tff(f_56, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 5.78/2.09  tff(f_128, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.78/2.09  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.78/2.09  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.78/2.09  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.78/2.09  tff(f_174, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 5.78/2.09  tff(f_142, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 5.78/2.09  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 5.78/2.09  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.78/2.09  tff(f_156, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 5.78/2.09  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.78/2.09  tff(f_185, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 5.78/2.09  tff(f_198, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 5.78/2.09  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(o_2_0_pre_topc(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_0_pre_topc)).
% 5.78/2.09  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 5.78/2.09  tff(f_107, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_2)).
% 5.78/2.09  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 5.78/2.09  tff(c_20, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.78/2.09  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 5.78/2.09  tff(c_14, plain, (![A_8]: (~v1_subset_1('#skF_1'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.78/2.09  tff(c_16, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.78/2.09  tff(c_1656, plain, (![B_253, A_254]: (v1_subset_1(B_253, A_254) | B_253=A_254 | ~m1_subset_1(B_253, k1_zfmisc_1(A_254)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.78/2.09  tff(c_1666, plain, (![A_8]: (v1_subset_1('#skF_1'(A_8), A_8) | '#skF_1'(A_8)=A_8)), inference(resolution, [status(thm)], [c_16, c_1656])).
% 5.78/2.09  tff(c_1671, plain, (![A_8]: ('#skF_1'(A_8)=A_8)), inference(negUnitSimplification, [status(thm)], [c_14, c_1666])).
% 5.78/2.09  tff(c_1674, plain, (![A_8]: (~v1_subset_1(A_8, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_14])).
% 5.78/2.09  tff(c_64, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 5.78/2.09  tff(c_80, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.78/2.09  tff(c_88, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_80])).
% 5.78/2.09  tff(c_89, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_88])).
% 5.78/2.09  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.78/2.09  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(k1_tarski(A_3), k1_zfmisc_1(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.78/2.09  tff(c_1814, plain, (![A_278, B_279]: (v1_subset_1(k1_tarski(A_278), B_279) | k1_tarski(A_278)=B_279 | ~r2_hidden(A_278, B_279))), inference(resolution, [status(thm)], [c_10, c_1656])).
% 5.78/2.09  tff(c_1718, plain, (![A_264, B_265]: (k6_domain_1(A_264, B_265)=k1_tarski(B_265) | ~m1_subset_1(B_265, A_264) | v1_xboole_0(A_264))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.78/2.09  tff(c_1730, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_1718])).
% 5.78/2.09  tff(c_1736, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_89, c_1730])).
% 5.78/2.09  tff(c_200, plain, (![A_86, B_87]: (k6_domain_1(A_86, B_87)=k1_tarski(B_87) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.78/2.09  tff(c_212, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_200])).
% 5.78/2.09  tff(c_218, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_89, c_212])).
% 5.78/2.09  tff(c_76, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 5.78/2.09  tff(c_90, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_76])).
% 5.78/2.09  tff(c_219, plain, (v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_90])).
% 5.78/2.09  tff(c_299, plain, (![A_100, B_101]: (~v1_zfmisc_1(A_100) | ~v1_subset_1(k6_domain_1(A_100, B_101), A_100) | ~m1_subset_1(B_101, A_100) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.78/2.09  tff(c_308, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_299])).
% 5.78/2.09  tff(c_314, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_219, c_308])).
% 5.78/2.09  tff(c_315, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_89, c_314])).
% 5.78/2.09  tff(c_459, plain, (![A_128, B_129]: (m1_pre_topc(k1_tex_2(A_128, B_129), A_128) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.78/2.09  tff(c_468, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_459])).
% 5.78/2.09  tff(c_474, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_468])).
% 5.78/2.09  tff(c_475, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_474])).
% 5.78/2.09  tff(c_778, plain, (![A_163, B_164]: (m1_subset_1('#skF_2'(A_163, B_164), k1_zfmisc_1(u1_struct_0(A_163))) | v1_tex_2(B_164, A_163) | ~m1_pre_topc(B_164, A_163) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.78/2.09  tff(c_40, plain, (![B_36, A_35]: (v1_subset_1(B_36, A_35) | B_36=A_35 | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.78/2.09  tff(c_1553, plain, (![A_233, B_234]: (v1_subset_1('#skF_2'(A_233, B_234), u1_struct_0(A_233)) | u1_struct_0(A_233)='#skF_2'(A_233, B_234) | v1_tex_2(B_234, A_233) | ~m1_pre_topc(B_234, A_233) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_778, c_40])).
% 5.78/2.09  tff(c_34, plain, (![A_25, B_31]: (~v1_subset_1('#skF_2'(A_25, B_31), u1_struct_0(A_25)) | v1_tex_2(B_31, A_25) | ~m1_pre_topc(B_31, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.78/2.09  tff(c_1566, plain, (![A_235, B_236]: (u1_struct_0(A_235)='#skF_2'(A_235, B_236) | v1_tex_2(B_236, A_235) | ~m1_pre_topc(B_236, A_235) | ~l1_pre_topc(A_235))), inference(resolution, [status(thm)], [c_1553, c_34])).
% 5.78/2.09  tff(c_70, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 5.78/2.09  tff(c_122, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_70])).
% 5.78/2.09  tff(c_1573, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1566, c_122])).
% 5.78/2.09  tff(c_1577, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_475, c_1573])).
% 5.78/2.09  tff(c_22, plain, (![B_16, A_14]: (l1_pre_topc(B_16) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.78/2.09  tff(c_478, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_475, c_22])).
% 5.78/2.09  tff(c_481, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_478])).
% 5.78/2.09  tff(c_395, plain, (![A_113, B_114]: (~v2_struct_0(k1_tex_2(A_113, B_114)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.78/2.09  tff(c_405, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_395])).
% 5.78/2.09  tff(c_410, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_405])).
% 5.78/2.09  tff(c_411, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_410])).
% 5.78/2.09  tff(c_487, plain, (![B_131, A_132]: (u1_struct_0(B_131)='#skF_2'(A_132, B_131) | v1_tex_2(B_131, A_132) | ~m1_pre_topc(B_131, A_132) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.78/2.09  tff(c_490, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_487, c_122])).
% 5.78/2.09  tff(c_493, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_475, c_490])).
% 5.78/2.09  tff(c_26, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.78/2.09  tff(c_547, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_26])).
% 5.78/2.09  tff(c_590, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_411, c_547])).
% 5.78/2.09  tff(c_592, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_590])).
% 5.78/2.09  tff(c_595, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_592])).
% 5.78/2.09  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_595])).
% 5.78/2.09  tff(c_600, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_590])).
% 5.78/2.09  tff(c_601, plain, (l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_590])).
% 5.78/2.09  tff(c_413, plain, (![A_116, B_117]: (v7_struct_0(k1_tex_2(A_116, B_117)) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l1_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.78/2.09  tff(c_423, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_413])).
% 5.78/2.09  tff(c_428, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_423])).
% 5.78/2.09  tff(c_429, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_428])).
% 5.78/2.09  tff(c_60, plain, (![A_47, B_49]: (v1_subset_1(k6_domain_1(A_47, B_49), A_47) | ~m1_subset_1(B_49, A_47) | v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.78/2.09  tff(c_947, plain, (![A_179, B_180]: (~v7_struct_0(A_179) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_179), B_180), u1_struct_0(A_179)) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_struct_0(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.78/2.09  tff(c_1191, plain, (![A_203, B_204]: (~v7_struct_0(A_203) | ~l1_struct_0(A_203) | v2_struct_0(A_203) | ~m1_subset_1(B_204, u1_struct_0(A_203)) | v1_zfmisc_1(u1_struct_0(A_203)) | v1_xboole_0(u1_struct_0(A_203)))), inference(resolution, [status(thm)], [c_60, c_947])).
% 5.78/2.09  tff(c_1197, plain, (![B_204]: (~v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_subset_1(B_204, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_493, c_1191])).
% 5.78/2.09  tff(c_1213, plain, (![B_204]: (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_subset_1(B_204, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_493, c_601, c_429, c_1197])).
% 5.78/2.09  tff(c_1214, plain, (![B_204]: (~m1_subset_1(B_204, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_600, c_411, c_1213])).
% 5.78/2.09  tff(c_1222, plain, (![B_204]: (~m1_subset_1(B_204, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))))), inference(splitLeft, [status(thm)], [c_1214])).
% 5.78/2.09  tff(c_138, plain, (![B_75, A_76]: (v1_subset_1(B_75, A_76) | B_75=A_76 | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.78/2.09  tff(c_148, plain, (![A_8]: (v1_subset_1('#skF_1'(A_8), A_8) | '#skF_1'(A_8)=A_8)), inference(resolution, [status(thm)], [c_16, c_138])).
% 5.78/2.09  tff(c_153, plain, (![A_8]: ('#skF_1'(A_8)=A_8)), inference(negUnitSimplification, [status(thm)], [c_14, c_148])).
% 5.78/2.09  tff(c_155, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_16])).
% 5.78/2.09  tff(c_364, plain, (![A_108, B_109]: (m1_subset_1(o_2_0_pre_topc(A_108, B_109), B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.78/2.09  tff(c_377, plain, (![A_108]: (m1_subset_1(o_2_0_pre_topc(A_108, u1_struct_0(A_108)), u1_struct_0(A_108)) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_155, c_364])).
% 5.78/2.09  tff(c_533, plain, (m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3', '#skF_4'), u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_377])).
% 5.78/2.09  tff(c_582, plain, (m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_493, c_533])).
% 5.78/2.09  tff(c_1224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1222, c_582])).
% 5.78/2.09  tff(c_1225, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1214])).
% 5.78/2.09  tff(c_1588, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1577, c_1225])).
% 5.78/2.09  tff(c_1606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_1588])).
% 5.78/2.09  tff(c_1607, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_76])).
% 5.78/2.09  tff(c_1610, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1607, c_70])).
% 5.78/2.09  tff(c_1737, plain, (~v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1736, c_1610])).
% 5.78/2.09  tff(c_1825, plain, (u1_struct_0('#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1814, c_1737])).
% 5.78/2.09  tff(c_1845, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1825])).
% 5.78/2.09  tff(c_1848, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_1845])).
% 5.78/2.09  tff(c_1851, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1848])).
% 5.78/2.09  tff(c_1853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_1851])).
% 5.78/2.09  tff(c_1854, plain, (u1_struct_0('#skF_3')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_1825])).
% 5.78/2.09  tff(c_1859, plain, (m1_subset_1('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_64])).
% 5.78/2.09  tff(c_2232, plain, (![A_305, B_306]: (m1_pre_topc(k1_tex_2(A_305, B_306), A_305) | ~m1_subset_1(B_306, u1_struct_0(A_305)) | ~l1_pre_topc(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.78/2.09  tff(c_2238, plain, (![B_306]: (m1_pre_topc(k1_tex_2('#skF_3', B_306), '#skF_3') | ~m1_subset_1(B_306, k1_tarski('#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_2232])).
% 5.78/2.09  tff(c_2245, plain, (![B_306]: (m1_pre_topc(k1_tex_2('#skF_3', B_306), '#skF_3') | ~m1_subset_1(B_306, k1_tarski('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2238])).
% 5.78/2.09  tff(c_2248, plain, (![B_307]: (m1_pre_topc(k1_tex_2('#skF_3', B_307), '#skF_3') | ~m1_subset_1(B_307, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_2245])).
% 5.78/2.09  tff(c_2260, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1859, c_2248])).
% 5.78/2.09  tff(c_2264, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2260, c_22])).
% 5.78/2.09  tff(c_2267, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2264])).
% 5.78/2.09  tff(c_1796, plain, (![A_272, B_273]: (~v2_struct_0(k1_tex_2(A_272, B_273)) | ~m1_subset_1(B_273, u1_struct_0(A_272)) | ~l1_pre_topc(A_272) | v2_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.78/2.09  tff(c_1803, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1796])).
% 5.78/2.09  tff(c_1807, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1803])).
% 5.78/2.09  tff(c_1808, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1807])).
% 5.78/2.09  tff(c_56, plain, (![B_43, A_41]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_pre_topc(B_43, A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.78/2.09  tff(c_1869, plain, (![B_43]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_pre_topc(B_43, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_56])).
% 5.78/2.09  tff(c_1945, plain, (![B_286]: (m1_subset_1(u1_struct_0(B_286), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_pre_topc(B_286, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1869])).
% 5.78/2.09  tff(c_2563, plain, (![B_337]: (v1_subset_1(u1_struct_0(B_337), k1_tarski('#skF_4')) | u1_struct_0(B_337)=k1_tarski('#skF_4') | ~m1_pre_topc(B_337, '#skF_3'))), inference(resolution, [status(thm)], [c_1945, c_40])).
% 5.78/2.09  tff(c_1858, plain, (~v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_89])).
% 5.78/2.09  tff(c_1857, plain, (k6_domain_1(k1_tarski('#skF_4'), '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_1736])).
% 5.78/2.09  tff(c_2040, plain, (![A_294, B_295]: (v1_subset_1(k6_domain_1(A_294, B_295), A_294) | ~m1_subset_1(B_295, A_294) | v1_zfmisc_1(A_294) | v1_xboole_0(A_294))), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.78/2.09  tff(c_2048, plain, (v1_subset_1(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | ~m1_subset_1('#skF_4', k1_tarski('#skF_4')) | v1_zfmisc_1(k1_tarski('#skF_4')) | v1_xboole_0(k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1857, c_2040])).
% 5.78/2.09  tff(c_2058, plain, (v1_subset_1(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | v1_zfmisc_1(k1_tarski('#skF_4')) | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1859, c_2048])).
% 5.78/2.09  tff(c_2059, plain, (v1_zfmisc_1(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1858, c_1674, c_2058])).
% 5.78/2.09  tff(c_1879, plain, (![B_43]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_pre_topc(B_43, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1869])).
% 5.78/2.09  tff(c_2095, plain, (![B_299, A_300]: (v1_xboole_0(B_299) | ~v1_subset_1(B_299, A_300) | ~m1_subset_1(B_299, k1_zfmisc_1(A_300)) | ~v1_zfmisc_1(A_300) | v1_xboole_0(A_300))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.78/2.09  tff(c_2101, plain, (![B_43]: (v1_xboole_0(u1_struct_0(B_43)) | ~v1_subset_1(u1_struct_0(B_43), k1_tarski('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_4')) | v1_xboole_0(k1_tarski('#skF_4')) | ~m1_pre_topc(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_1879, c_2095])).
% 5.78/2.09  tff(c_2120, plain, (![B_43]: (v1_xboole_0(u1_struct_0(B_43)) | ~v1_subset_1(u1_struct_0(B_43), k1_tarski('#skF_4')) | v1_xboole_0(k1_tarski('#skF_4')) | ~m1_pre_topc(B_43, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2059, c_2101])).
% 5.78/2.09  tff(c_2121, plain, (![B_43]: (v1_xboole_0(u1_struct_0(B_43)) | ~v1_subset_1(u1_struct_0(B_43), k1_tarski('#skF_4')) | ~m1_pre_topc(B_43, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1858, c_2120])).
% 5.78/2.09  tff(c_2576, plain, (![B_338]: (v1_xboole_0(u1_struct_0(B_338)) | u1_struct_0(B_338)=k1_tarski('#skF_4') | ~m1_pre_topc(B_338, '#skF_3'))), inference(resolution, [status(thm)], [c_2563, c_2121])).
% 5.78/2.09  tff(c_2593, plain, (![B_339]: (~l1_struct_0(B_339) | v2_struct_0(B_339) | u1_struct_0(B_339)=k1_tarski('#skF_4') | ~m1_pre_topc(B_339, '#skF_3'))), inference(resolution, [status(thm)], [c_2576, c_26])).
% 5.78/2.09  tff(c_2603, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_2260, c_2593])).
% 5.78/2.09  tff(c_2613, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1808, c_2603])).
% 5.78/2.09  tff(c_2614, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2613])).
% 5.78/2.09  tff(c_2617, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_2614])).
% 5.78/2.09  tff(c_2621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2267, c_2617])).
% 5.78/2.09  tff(c_2622, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_2613])).
% 5.78/2.09  tff(c_2864, plain, (![B_342, A_343]: (v1_subset_1(u1_struct_0(B_342), u1_struct_0(A_343)) | ~m1_subset_1(u1_struct_0(B_342), k1_zfmisc_1(u1_struct_0(A_343))) | ~v1_tex_2(B_342, A_343) | ~m1_pre_topc(B_342, A_343) | ~l1_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.78/2.09  tff(c_3466, plain, (![B_365, A_366]: (v1_subset_1(u1_struct_0(B_365), u1_struct_0(A_366)) | ~v1_tex_2(B_365, A_366) | ~m1_pre_topc(B_365, A_366) | ~l1_pre_topc(A_366))), inference(resolution, [status(thm)], [c_56, c_2864])).
% 5.78/2.09  tff(c_3493, plain, (![B_365]: (v1_subset_1(u1_struct_0(B_365), k1_tarski('#skF_4')) | ~v1_tex_2(B_365, '#skF_3') | ~m1_pre_topc(B_365, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_3466])).
% 5.78/2.09  tff(c_3519, plain, (![B_369]: (v1_subset_1(u1_struct_0(B_369), k1_tarski('#skF_4')) | ~v1_tex_2(B_369, '#skF_3') | ~m1_pre_topc(B_369, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3493])).
% 5.78/2.09  tff(c_3530, plain, (v1_subset_1(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2622, c_3519])).
% 5.78/2.09  tff(c_3541, plain, (v1_subset_1(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2260, c_1607, c_3530])).
% 5.78/2.09  tff(c_3543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1674, c_3541])).
% 5.78/2.09  tff(c_3545, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_88])).
% 5.78/2.09  tff(c_3550, plain, (![A_374]: (~v1_xboole_0(u1_struct_0(A_374)) | ~l1_struct_0(A_374) | v2_struct_0(A_374))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.78/2.09  tff(c_3553, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3545, c_3550])).
% 5.78/2.09  tff(c_3556, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_3553])).
% 5.78/2.09  tff(c_3569, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3556])).
% 5.78/2.09  tff(c_3573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3569])).
% 5.78/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.09  
% 5.78/2.09  Inference rules
% 5.78/2.09  ----------------------
% 5.78/2.09  #Ref     : 0
% 5.78/2.09  #Sup     : 706
% 5.78/2.09  #Fact    : 0
% 5.78/2.09  #Define  : 0
% 5.78/2.09  #Split   : 17
% 5.78/2.09  #Chain   : 0
% 5.78/2.09  #Close   : 0
% 5.78/2.09  
% 5.78/2.09  Ordering : KBO
% 5.78/2.09  
% 5.78/2.09  Simplification rules
% 5.78/2.09  ----------------------
% 5.78/2.09  #Subsume      : 170
% 5.78/2.09  #Demod        : 451
% 5.78/2.09  #Tautology    : 148
% 5.78/2.09  #SimpNegUnit  : 159
% 5.78/2.09  #BackRed      : 48
% 5.78/2.09  
% 5.78/2.09  #Partial instantiations: 0
% 5.78/2.09  #Strategies tried      : 1
% 5.78/2.09  
% 5.78/2.09  Timing (in seconds)
% 5.78/2.09  ----------------------
% 5.78/2.10  Preprocessing        : 0.40
% 5.78/2.10  Parsing              : 0.22
% 5.78/2.10  CNF conversion       : 0.03
% 5.78/2.10  Main loop            : 0.88
% 5.78/2.10  Inferencing          : 0.33
% 5.78/2.10  Reduction            : 0.28
% 5.78/2.10  Demodulation         : 0.19
% 5.78/2.10  BG Simplification    : 0.04
% 5.78/2.10  Subsumption          : 0.16
% 5.78/2.10  Abstraction          : 0.04
% 5.78/2.10  MUC search           : 0.00
% 5.78/2.10  Cooper               : 0.00
% 5.78/2.10  Total                : 1.33
% 5.78/2.10  Index Insertion      : 0.00
% 5.78/2.10  Index Deletion       : 0.00
% 5.78/2.10  Index Matching       : 0.00
% 5.78/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
