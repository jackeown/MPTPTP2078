%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:07 EST 2020

% Result     : Theorem 28.10s
% Output     : CNFRefutation 28.75s
% Verified   : 
% Statistics : Number of formulae       :  555 (1045181 expanded)
%              Number of leaves         :   44 (349614 expanded)
%              Depth                    :   61
%              Number of atoms          : 1572 (4085669 expanded)
%              Number of equality atoms :  198 (306209 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_252,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_194,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & ~ v2_struct_0(B)
          & v1_pre_topc(B)
          & ~ v1_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_tex_2)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_207,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & ~ v2_struct_0(B)
          & v1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_220,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_95,axiom,(
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

tff(f_178,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_164,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_66,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_78,plain,(
    ! [B_60,A_61] :
      ( l1_pre_topc(B_60)
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_78])).

tff(c_84,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_81])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    v7_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_91,plain,(
    ! [A_68] :
      ( m1_pre_topc('#skF_3'(A_68),A_68)
      | ~ l1_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [A_68] :
      ( l1_pre_topc('#skF_3'(A_68))
      | ~ l1_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_56,plain,(
    ! [A_41] :
      ( m1_pre_topc('#skF_3'(A_41),A_41)
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_4,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_289,plain,(
    ! [B_122,A_123] :
      ( g1_pre_topc(u1_struct_0(B_122),u1_pre_topc(B_122)) = g1_pre_topc(u1_struct_0(A_123),u1_pre_topc(A_123))
      | ~ m1_pre_topc(B_122,A_123)
      | v1_tex_2(B_122,A_123)
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_24,plain,(
    ! [B_23,A_21] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_23),u1_pre_topc(B_23)),A_21)
      | ~ m1_pre_topc(B_23,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7438,plain,(
    ! [B_2515,A_2516,A_2517] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_2515),u1_pre_topc(B_2515)),A_2516)
      | ~ m1_pre_topc(A_2517,A_2516)
      | ~ l1_pre_topc(A_2516)
      | ~ m1_pre_topc(B_2515,A_2517)
      | v1_tex_2(B_2515,A_2517)
      | ~ l1_pre_topc(A_2517)
      | v2_struct_0(A_2517) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_24])).

tff(c_7472,plain,(
    ! [B_2515] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_2515),u1_pre_topc(B_2515)),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_2515,'#skF_5')
      | v1_tex_2(B_2515,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_7438])).

tff(c_7480,plain,(
    ! [B_2515] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_2515),u1_pre_topc(B_2515)),'#skF_4')
      | ~ m1_pre_topc(B_2515,'#skF_5')
      | v1_tex_2(B_2515,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_7472])).

tff(c_7482,plain,(
    ! [B_2542] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_2542),u1_pre_topc(B_2542)),'#skF_4')
      | ~ m1_pre_topc(B_2542,'#skF_5')
      | v1_tex_2(B_2542,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7480])).

tff(c_7691,plain,(
    ! [A_2567] :
      ( m1_pre_topc(A_2567,'#skF_4')
      | ~ m1_pre_topc(A_2567,'#skF_5')
      | v1_tex_2(A_2567,'#skF_5')
      | ~ v1_pre_topc(A_2567)
      | ~ l1_pre_topc(A_2567) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7482])).

tff(c_30,plain,(
    ! [B_29,A_27] :
      ( ~ v1_tex_2(B_29,A_27)
      | v2_struct_0(B_29)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v7_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7698,plain,(
    ! [A_2567] :
      ( v2_struct_0(A_2567)
      | ~ l1_pre_topc('#skF_5')
      | ~ v7_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | m1_pre_topc(A_2567,'#skF_4')
      | ~ m1_pre_topc(A_2567,'#skF_5')
      | ~ v1_pre_topc(A_2567)
      | ~ l1_pre_topc(A_2567) ) ),
    inference(resolution,[status(thm)],[c_7691,c_30])).

tff(c_7709,plain,(
    ! [A_2567] :
      ( v2_struct_0(A_2567)
      | v2_struct_0('#skF_5')
      | m1_pre_topc(A_2567,'#skF_4')
      | ~ m1_pre_topc(A_2567,'#skF_5')
      | ~ v1_pre_topc(A_2567)
      | ~ l1_pre_topc(A_2567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_84,c_7698])).

tff(c_7715,plain,(
    ! [A_2592] :
      ( v2_struct_0(A_2592)
      | m1_pre_topc(A_2592,'#skF_4')
      | ~ m1_pre_topc(A_2592,'#skF_5')
      | ~ v1_pre_topc(A_2592)
      | ~ l1_pre_topc(A_2592) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7709])).

tff(c_7735,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | m1_pre_topc('#skF_3'('#skF_5'),'#skF_4')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_7715])).

tff(c_7753,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | m1_pre_topc('#skF_3'('#skF_5'),'#skF_4')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7735])).

tff(c_7754,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | m1_pre_topc('#skF_3'('#skF_5'),'#skF_4')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7753])).

tff(c_8053,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7754])).

tff(c_8056,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_8053])).

tff(c_8059,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8056])).

tff(c_8061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8059])).

tff(c_8063,plain,(
    l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7754])).

tff(c_58,plain,(
    ! [B_45,A_43] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = g1_pre_topc(u1_struct_0(A_43),u1_pre_topc(A_43))
      | ~ m1_pre_topc(B_45,A_43)
      | v1_tex_2(B_45,A_43)
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_52,plain,(
    ! [A_41] :
      ( v1_pre_topc('#skF_3'(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_8062,plain,
    ( ~ v1_pre_topc('#skF_3'('#skF_5'))
    | m1_pre_topc('#skF_3'('#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7754])).

tff(c_8233,plain,(
    ~ v1_pre_topc('#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8062])).

tff(c_8236,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_8233])).

tff(c_8239,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8236])).

tff(c_8241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8239])).

tff(c_8242,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | m1_pre_topc('#skF_3'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8062])).

tff(c_8316,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8242])).

tff(c_26,plain,(
    ! [B_23,A_21] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_23),u1_pre_topc(B_23)))
      | ~ m1_pre_topc(B_23,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8337,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8316,c_26])).

tff(c_8373,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8337])).

tff(c_8679,plain,(
    ! [B_45] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)))
      | ~ m1_pre_topc(B_45,'#skF_3'('#skF_5'))
      | v1_tex_2(B_45,'#skF_3'('#skF_5'))
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_8373])).

tff(c_8724,plain,(
    ! [B_45] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)))
      | ~ m1_pre_topc(B_45,'#skF_3'('#skF_5'))
      | v1_tex_2(B_45,'#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8679])).

tff(c_80551,plain,(
    v2_struct_0('#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8724])).

tff(c_54,plain,(
    ! [A_41] :
      ( ~ v2_struct_0('#skF_3'(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_80554,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80551,c_54])).

tff(c_80557,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80554])).

tff(c_80559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80557])).

tff(c_80561,plain,(
    ~ v2_struct_0('#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8724])).

tff(c_8243,plain,(
    v1_pre_topc('#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8062])).

tff(c_3102,plain,(
    ! [A_1125,A_1126] :
      ( g1_pre_topc(u1_struct_0(A_1125),u1_pre_topc(A_1125)) = A_1126
      | ~ m1_pre_topc(A_1126,A_1125)
      | v1_tex_2(A_1126,A_1125)
      | ~ l1_pre_topc(A_1125)
      | v2_struct_0(A_1125)
      | ~ v1_pre_topc(A_1126)
      | ~ l1_pre_topc(A_1126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_289])).

tff(c_6549,plain,(
    ! [A_2138,A_2137] :
      ( A_2138 = A_2137
      | ~ m1_pre_topc(A_2138,A_2137)
      | v1_tex_2(A_2138,A_2137)
      | ~ l1_pre_topc(A_2137)
      | v2_struct_0(A_2137)
      | ~ v1_pre_topc(A_2138)
      | ~ l1_pre_topc(A_2138)
      | ~ v1_pre_topc(A_2137)
      | ~ l1_pre_topc(A_2137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3102])).

tff(c_50,plain,(
    ! [A_41] :
      ( ~ v1_tex_2('#skF_3'(A_41),A_41)
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_6592,plain,(
    ! [A_2189] :
      ( '#skF_3'(A_2189) = A_2189
      | ~ m1_pre_topc('#skF_3'(A_2189),A_2189)
      | v2_struct_0(A_2189)
      | ~ v1_pre_topc('#skF_3'(A_2189))
      | ~ l1_pre_topc('#skF_3'(A_2189))
      | ~ v1_pre_topc(A_2189)
      | ~ l1_pre_topc(A_2189) ) ),
    inference(resolution,[status(thm)],[c_6549,c_50])).

tff(c_6603,plain,(
    ! [A_2214] :
      ( '#skF_3'(A_2214) = A_2214
      | ~ v1_pre_topc('#skF_3'(A_2214))
      | ~ l1_pre_topc('#skF_3'(A_2214))
      | ~ v1_pre_topc(A_2214)
      | ~ l1_pre_topc(A_2214)
      | v2_struct_0(A_2214) ) ),
    inference(resolution,[status(thm)],[c_56,c_6592])).

tff(c_6614,plain,(
    ! [A_2239] :
      ( '#skF_3'(A_2239) = A_2239
      | ~ l1_pre_topc('#skF_3'(A_2239))
      | ~ v1_pre_topc(A_2239)
      | ~ l1_pre_topc(A_2239)
      | v2_struct_0(A_2239) ) ),
    inference(resolution,[status(thm)],[c_52,c_6603])).

tff(c_6624,plain,(
    ! [A_68] :
      ( '#skF_3'(A_68) = A_68
      | ~ v1_pre_topc(A_68)
      | ~ l1_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_95,c_6614])).

tff(c_80564,plain,
    ( '#skF_3'('#skF_3'('#skF_5')) = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6624,c_80561])).

tff(c_80567,plain,(
    '#skF_3'('#skF_3'('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_80564])).

tff(c_80613,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80567,c_56])).

tff(c_80669,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_80613])).

tff(c_80670,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_80669])).

tff(c_98,plain,(
    ! [A_71] :
      ( m1_pre_topc('#skF_2'(A_71),A_71)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_102,plain,(
    ! [A_71] :
      ( l1_pre_topc('#skF_2'(A_71))
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_98,c_8])).

tff(c_18,plain,(
    ! [A_10] :
      ( m1_pre_topc('#skF_2'(A_10),A_10)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7731,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | m1_pre_topc('#skF_2'('#skF_5'),'#skF_4')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_7715])).

tff(c_7749,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | m1_pre_topc('#skF_2'('#skF_5'),'#skF_4')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7731])).

tff(c_7750,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | m1_pre_topc('#skF_2'('#skF_5'),'#skF_4')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7749])).

tff(c_7755,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7750])).

tff(c_7758,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_7755])).

tff(c_7761,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7758])).

tff(c_7763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7761])).

tff(c_7765,plain,(
    l1_pre_topc('#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7750])).

tff(c_14,plain,(
    ! [A_10] :
      ( v1_pre_topc('#skF_2'(A_10))
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7764,plain,
    ( ~ v1_pre_topc('#skF_2'('#skF_5'))
    | m1_pre_topc('#skF_2'('#skF_5'),'#skF_4')
    | v2_struct_0('#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7750])).

tff(c_7766,plain,(
    ~ v1_pre_topc('#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7764])).

tff(c_7769,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_7766])).

tff(c_7772,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7769])).

tff(c_7774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7772])).

tff(c_7775,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | m1_pre_topc('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7764])).

tff(c_7825,plain,(
    m1_pre_topc('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7775])).

tff(c_173,plain,(
    ! [B_90,A_91] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_90),u1_pre_topc(B_90)),A_91)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_183,plain,(
    ! [B_90,A_91] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_90),u1_pre_topc(B_90)))
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_7844,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')),u1_pre_topc('#skF_2'('#skF_5'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_7825,c_183])).

tff(c_7879,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')),u1_pre_topc('#skF_2'('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7844])).

tff(c_8007,plain,(
    ! [B_45] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)))
      | ~ m1_pre_topc(B_45,'#skF_2'('#skF_5'))
      | v1_tex_2(B_45,'#skF_2'('#skF_5'))
      | ~ l1_pre_topc('#skF_2'('#skF_5'))
      | v2_struct_0('#skF_2'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_7879])).

tff(c_8050,plain,(
    ! [B_45] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)))
      | ~ m1_pre_topc(B_45,'#skF_2'('#skF_5'))
      | v1_tex_2(B_45,'#skF_2'('#skF_5'))
      | v2_struct_0('#skF_2'('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_8007])).

tff(c_9885,plain,(
    v2_struct_0('#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8050])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v2_struct_0('#skF_2'(A_10))
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10597,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_9885,c_16])).

tff(c_10600,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10597])).

tff(c_10602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_10600])).

tff(c_10604,plain,(
    ~ v2_struct_0('#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8050])).

tff(c_7776,plain,(
    v1_pre_topc('#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7764])).

tff(c_383,plain,(
    ! [A_123,A_3] :
      ( g1_pre_topc(u1_struct_0(A_123),u1_pre_topc(A_123)) = A_3
      | ~ m1_pre_topc(A_3,A_123)
      | v1_tex_2(A_3,A_123)
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123)
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_289])).

tff(c_12,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [B_26,A_24] :
      ( r1_tarski(u1_struct_0(B_26),u1_struct_0(A_24))
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_131,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(A_80,B_79)
      | ~ v1_zfmisc_1(B_79)
      | v1_xboole_0(B_79)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_445,plain,(
    ! [B_132,A_133] :
      ( u1_struct_0(B_132) = u1_struct_0(A_133)
      | ~ v1_zfmisc_1(u1_struct_0(A_133))
      | v1_xboole_0(u1_struct_0(A_133))
      | v1_xboole_0(u1_struct_0(B_132))
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_28,c_131])).

tff(c_537,plain,(
    ! [B_141,A_142] :
      ( u1_struct_0(B_141) = u1_struct_0(A_142)
      | v1_xboole_0(u1_struct_0(A_142))
      | v1_xboole_0(u1_struct_0(B_141))
      | ~ m1_pre_topc(B_141,A_142)
      | ~ l1_pre_topc(A_142)
      | ~ l1_struct_0(A_142)
      | ~ v7_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_12,c_445])).

tff(c_554,plain,(
    ! [A_41] :
      ( u1_struct_0('#skF_3'(A_41)) = u1_struct_0(A_41)
      | v1_xboole_0(u1_struct_0(A_41))
      | v1_xboole_0(u1_struct_0('#skF_3'(A_41)))
      | ~ l1_struct_0(A_41)
      | ~ v7_struct_0(A_41)
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_56,c_537])).

tff(c_12486,plain,(
    v2_struct_0('#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8724])).

tff(c_12489,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12486,c_54])).

tff(c_12492,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_12489])).

tff(c_12494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_12492])).

tff(c_12496,plain,(
    ~ v2_struct_0('#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8724])).

tff(c_12499,plain,
    ( '#skF_3'('#skF_3'('#skF_5')) = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6624,c_12496])).

tff(c_12502,plain,(
    '#skF_3'('#skF_3'('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_12499])).

tff(c_12548,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12502,c_56])).

tff(c_12604,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_12548])).

tff(c_12605,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_12604])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_247,plain,(
    ! [C_109,A_110,B_111] :
      ( m1_subset_1(C_109,u1_struct_0(A_110))
      | ~ m1_subset_1(C_109,u1_struct_0(B_111))
      | ~ m1_pre_topc(B_111,A_110)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_252,plain,(
    ! [B_112,A_113] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_112)),u1_struct_0(A_113))
      | ~ m1_pre_topc(B_112,A_113)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_2,c_247])).

tff(c_20,plain,(
    ! [C_18,A_12,B_16] :
      ( m1_subset_1(C_18,u1_struct_0(A_12))
      | ~ m1_subset_1(C_18,u1_struct_0(B_16))
      | ~ m1_pre_topc(B_16,A_12)
      | v2_struct_0(B_16)
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_43297,plain,(
    ! [B_6857,A_6858,A_6859] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_6857)),u1_struct_0(A_6858))
      | ~ m1_pre_topc(A_6859,A_6858)
      | ~ l1_pre_topc(A_6858)
      | v2_struct_0(A_6858)
      | ~ m1_pre_topc(B_6857,A_6859)
      | v2_struct_0(B_6857)
      | ~ l1_pre_topc(A_6859)
      | v2_struct_0(A_6859) ) ),
    inference(resolution,[status(thm)],[c_252,c_20])).

tff(c_43311,plain,(
    ! [B_6857] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_6857)),u1_struct_0('#skF_3'('#skF_5')))
      | ~ m1_pre_topc(B_6857,'#skF_3'('#skF_5'))
      | v2_struct_0(B_6857)
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12605,c_43297])).

tff(c_43363,plain,(
    ! [B_6857] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_6857)),u1_struct_0('#skF_3'('#skF_5')))
      | ~ m1_pre_topc(B_6857,'#skF_3'('#skF_5'))
      | v2_struct_0(B_6857)
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_43311])).

tff(c_44962,plain,(
    ! [B_7410] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_7410)),u1_struct_0('#skF_3'('#skF_5')))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_43363])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k6_domain_1(A_19,B_20) = k1_tarski(B_20)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_45010,plain,(
    ! [B_7410] :
      ( k6_domain_1(u1_struct_0('#skF_3'('#skF_5')),'#skF_1'(u1_struct_0(B_7410))) = k1_tarski('#skF_1'(u1_struct_0(B_7410)))
      | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(resolution,[status(thm)],[c_44962,c_22])).

tff(c_58581,plain,(
    v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_45010])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58584,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58581,c_10])).

tff(c_58587,plain,(
    ~ l1_struct_0('#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_58584])).

tff(c_58590,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_58587])).

tff(c_58594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_58590])).

tff(c_58596,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_45010])).

tff(c_58599,plain,
    ( u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_554,c_58596])).

tff(c_58602,plain,
    ( u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_68,c_58599])).

tff(c_58603,plain,
    ( u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_58602])).

tff(c_58604,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58603])).

tff(c_58607,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_58604])).

tff(c_58611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_58607])).

tff(c_58613,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_58603])).

tff(c_661,plain,(
    ! [B_146,A_147] :
      ( g1_pre_topc(u1_struct_0(B_146),u1_pre_topc(B_146)) = A_147
      | ~ m1_pre_topc(B_146,A_147)
      | v1_tex_2(B_146,A_147)
      | ~ l1_pre_topc(A_147)
      | v2_struct_0(A_147)
      | ~ v1_pre_topc(A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_289])).

tff(c_2937,plain,(
    ! [B_1098,A_1099] :
      ( v2_struct_0(B_1098)
      | ~ v7_struct_0(A_1099)
      | g1_pre_topc(u1_struct_0(B_1098),u1_pre_topc(B_1098)) = A_1099
      | ~ m1_pre_topc(B_1098,A_1099)
      | v2_struct_0(A_1099)
      | ~ v1_pre_topc(A_1099)
      | ~ l1_pre_topc(A_1099) ) ),
    inference(resolution,[status(thm)],[c_661,c_30])).

tff(c_2965,plain,(
    ! [A_41] :
      ( v2_struct_0('#skF_3'(A_41))
      | ~ v7_struct_0(A_41)
      | g1_pre_topc(u1_struct_0('#skF_3'(A_41)),u1_pre_topc('#skF_3'(A_41))) = A_41
      | ~ v1_pre_topc(A_41)
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_56,c_2937])).

tff(c_12527,plain,
    ( v2_struct_0('#skF_3'('#skF_3'('#skF_5')))
    | ~ v7_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_3'('#skF_5'))),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12502,c_2965])).

tff(c_12583,plain,
    ( ~ v7_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_12502,c_12502,c_12527])).

tff(c_12584,plain,
    ( ~ v7_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_12583])).

tff(c_12698,plain,(
    ~ v7_struct_0('#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_12584])).

tff(c_58612,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_58603])).

tff(c_58614,plain,(
    u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58612])).

tff(c_153,plain,(
    ! [A_83,B_84] :
      ( ~ v2_struct_0(k1_tex_2(A_83,B_84))
      | ~ m1_subset_1(B_84,u1_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_158,plain,(
    ! [A_83] :
      ( ~ v2_struct_0(k1_tex_2(A_83,'#skF_1'(u1_struct_0(A_83))))
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_2,c_153])).

tff(c_59291,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_158])).

tff(c_59741,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_59291])).

tff(c_59742,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_59741])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( m1_pre_topc(k1_tex_2(A_37,B_38),A_37)
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_44966,plain,(
    ! [B_7410] :
      ( m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0(B_7410))),'#skF_3'('#skF_5'))
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(resolution,[status(thm)],[c_44962,c_38])).

tff(c_44996,plain,(
    ! [B_7410] :
      ( m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0(B_7410))),'#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_44966])).

tff(c_44997,plain,(
    ! [B_7410] :
      ( m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0(B_7410))),'#skF_3'('#skF_5'))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_44996])).

tff(c_58863,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_44997])).

tff(c_59470,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12605,c_58863])).

tff(c_59471,plain,(
    m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_59470])).

tff(c_58615,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58614,c_58596])).

tff(c_43364,plain,(
    ! [B_6857] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_6857)),u1_struct_0('#skF_3'('#skF_5')))
      | ~ m1_pre_topc(B_6857,'#skF_3'('#skF_5'))
      | v2_struct_0(B_6857) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_43363])).

tff(c_64036,plain,(
    ! [B_11085] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_11085)),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58614,c_43364])).

tff(c_48,plain,(
    ! [A_39,B_40] :
      ( ~ v2_struct_0(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_64052,plain,(
    ! [B_11085] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(resolution,[status(thm)],[c_64036,c_48])).

tff(c_64092,plain,(
    ! [B_11085] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64052])).

tff(c_64146,plain,(
    ! [B_11159] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11159))))
      | ~ m1_pre_topc(B_11159,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64092])).

tff(c_64152,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_64146])).

tff(c_64176,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12605,c_64152])).

tff(c_64177,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_64176])).

tff(c_44,plain,(
    ! [A_39,B_40] :
      ( v1_pre_topc(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_64049,plain,(
    ! [B_11085] :
      ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(resolution,[status(thm)],[c_64036,c_44])).

tff(c_64088,plain,(
    ! [B_11085] :
      ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64049])).

tff(c_64190,plain,(
    ! [B_11208] :
      ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11208))))
      | ~ m1_pre_topc(B_11208,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64088])).

tff(c_64196,plain,
    ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_64190])).

tff(c_64217,plain,
    ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12605,c_64196])).

tff(c_64218,plain,(
    v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_64217])).

tff(c_64043,plain,(
    ! [B_11085] :
      ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))),'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(resolution,[status(thm)],[c_64036,c_38])).

tff(c_64080,plain,(
    ! [B_11085] :
      ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))),'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64043])).

tff(c_65372,plain,(
    ! [B_11526] :
      ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11526))),'#skF_5')
      | ~ m1_pre_topc(B_11526,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11526) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64080])).

tff(c_65424,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))),'#skF_5')
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_65372])).

tff(c_65510,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))),'#skF_5')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12605,c_65424])).

tff(c_65511,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_65510])).

tff(c_36,plain,(
    ! [A_30,B_34] :
      ( k6_domain_1(u1_struct_0(A_30),B_34) = u1_struct_0(k1_tex_2(A_30,B_34))
      | ~ m1_pre_topc(k1_tex_2(A_30,B_34),A_30)
      | ~ v1_pre_topc(k1_tex_2(A_30,B_34))
      | v2_struct_0(k1_tex_2(A_30,B_34))
      | ~ m1_subset_1(B_34,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_65544,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_65511,c_36])).

tff(c_65620,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2,c_64218,c_65544])).

tff(c_65621,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64177,c_65620])).

tff(c_117,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_121,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_65695,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5')))) = k1_tarski('#skF_1'(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_65621,c_121])).

tff(c_65716,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5')))) = k1_tarski('#skF_1'(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58615,c_65695])).

tff(c_65724,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = k1_tarski('#skF_1'(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65716,c_65621])).

tff(c_44972,plain,(
    ! [B_7410] :
      ( v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0(B_7410))))
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(resolution,[status(thm)],[c_44962,c_44])).

tff(c_45004,plain,(
    ! [B_7410] :
      ( v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0(B_7410))))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_44972])).

tff(c_45005,plain,(
    ! [B_7410] :
      ( v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0(B_7410))))
      | ~ m1_pre_topc(B_7410,'#skF_3'('#skF_5'))
      | v2_struct_0(B_7410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_45004])).

tff(c_58875,plain,
    ( v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_45005])).

tff(c_59480,plain,
    ( v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12605,c_58875])).

tff(c_59481,plain,(
    v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_59480])).

tff(c_61608,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'('#skF_5')),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_3'('#skF_5')))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_59471,c_36])).

tff(c_61661,plain,
    ( u1_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) = k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_2,c_58614,c_59481,c_58614,c_61608])).

tff(c_61662,plain,(
    u1_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) = k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_59742,c_61661])).

tff(c_68576,plain,(
    u1_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) = k1_tarski('#skF_1'(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65724,c_61662])).

tff(c_64093,plain,(
    ! [B_11085] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64092])).

tff(c_68598,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | ~ m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68576,c_64093])).

tff(c_69077,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59471,c_68598])).

tff(c_69078,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_59742,c_69077])).

tff(c_65418,plain,(
    ! [B_11526] :
      ( l1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11526))))
      | ~ l1_pre_topc('#skF_5')
      | ~ m1_pre_topc(B_11526,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11526) ) ),
    inference(resolution,[status(thm)],[c_65372,c_8])).

tff(c_65507,plain,(
    ! [B_11526] :
      ( l1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11526))))
      | ~ m1_pre_topc(B_11526,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11526) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_65418])).

tff(c_68589,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | ~ m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68576,c_65507])).

tff(c_69068,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59471,c_68589])).

tff(c_69069,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_59742,c_69068])).

tff(c_64089,plain,(
    ! [B_11085] :
      ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64088])).

tff(c_68595,plain,
    ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | ~ m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68576,c_64089])).

tff(c_69074,plain,
    ( v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59471,c_68595])).

tff(c_69075,plain,(
    v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_59742,c_69074])).

tff(c_59303,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_4])).

tff(c_59749,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_59303])).

tff(c_6625,plain,(
    ! [B_2264,A_2265] :
      ( v2_struct_0(B_2264)
      | ~ v7_struct_0(A_2265)
      | g1_pre_topc(u1_struct_0(B_2264),u1_pre_topc(B_2264)) = g1_pre_topc(u1_struct_0(A_2265),u1_pre_topc(A_2265))
      | ~ m1_pre_topc(B_2264,A_2265)
      | ~ l1_pre_topc(A_2265)
      | v2_struct_0(A_2265) ) ),
    inference(resolution,[status(thm)],[c_289,c_30])).

tff(c_6686,plain,(
    ! [A_41] :
      ( v2_struct_0('#skF_3'(A_41))
      | ~ v7_struct_0(A_41)
      | g1_pre_topc(u1_struct_0('#skF_3'(A_41)),u1_pre_topc('#skF_3'(A_41))) = g1_pre_topc(u1_struct_0(A_41),u1_pre_topc(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_56,c_6625])).

tff(c_59055,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | ~ v7_struct_0('#skF_5')
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_3'('#skF_5'))) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_58614,c_6686])).

tff(c_59587,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_3'('#skF_5'))) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_68,c_59055])).

tff(c_59588,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_3'('#skF_5'))) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_12496,c_59587])).

tff(c_60438,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59749,c_59588])).

tff(c_64081,plain,(
    ! [B_11085] :
      ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))),'#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64080])).

tff(c_68592,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))),'#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68576,c_64081])).

tff(c_69071,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))),'#skF_5')
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59471,c_68592])).

tff(c_69072,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_59742,c_69071])).

tff(c_5806,plain,(
    ! [A_1126,A_1125] :
      ( v2_struct_0(A_1126)
      | ~ v7_struct_0(A_1125)
      | g1_pre_topc(u1_struct_0(A_1125),u1_pre_topc(A_1125)) = A_1126
      | ~ m1_pre_topc(A_1126,A_1125)
      | ~ l1_pre_topc(A_1125)
      | v2_struct_0(A_1125)
      | ~ v1_pre_topc(A_1126)
      | ~ l1_pre_topc(A_1126) ) ),
    inference(resolution,[status(thm)],[c_3102,c_30])).

tff(c_69745,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | ~ v7_struct_0('#skF_5')
    | k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ v1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) ),
    inference(resolution,[status(thm)],[c_69072,c_5806])).

tff(c_69828,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))) = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69069,c_69075,c_84,c_60438,c_68,c_69745])).

tff(c_69829,plain,(
    k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))) = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_69078,c_69828])).

tff(c_46,plain,(
    ! [A_39,B_40] :
      ( v7_struct_0(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_64046,plain,(
    ! [B_11085] :
      ( v7_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(resolution,[status(thm)],[c_64036,c_46])).

tff(c_64084,plain,(
    ! [B_11085] :
      ( v7_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64046])).

tff(c_64085,plain,(
    ! [B_11085] :
      ( v7_struct_0(k1_tex_2('#skF_5','#skF_1'(u1_struct_0(B_11085))))
      | ~ m1_pre_topc(B_11085,'#skF_3'('#skF_5'))
      | v2_struct_0(B_11085) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64084])).

tff(c_68601,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | ~ m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_68576,c_64085])).

tff(c_69080,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59471,c_68601])).

tff(c_69081,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_59742,c_69080])).

tff(c_70104,plain,(
    v7_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69829,c_69081])).

tff(c_70109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12698,c_70104])).

tff(c_70110,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58612])).

tff(c_70114,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70110,c_10])).

tff(c_70117,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58613,c_70114])).

tff(c_70119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70117])).

tff(c_70121,plain,(
    v7_struct_0('#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_12584])).

tff(c_70120,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12584])).

tff(c_70340,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_3'('#skF_5'))
      | v1_tex_2(B_45,'#skF_3'('#skF_5'))
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_70120])).

tff(c_70449,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_3'('#skF_5'))
      | v1_tex_2(B_45,'#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_70340])).

tff(c_71367,plain,(
    ! [B_12872] :
      ( g1_pre_topc(u1_struct_0(B_12872),u1_pre_topc(B_12872)) = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(B_12872,'#skF_3'('#skF_5'))
      | v1_tex_2(B_12872,'#skF_3'('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_70449])).

tff(c_72899,plain,(
    ! [A_13074,B_13075] :
      ( m1_pre_topc('#skF_3'('#skF_5'),A_13074)
      | ~ m1_pre_topc(B_13075,A_13074)
      | ~ l1_pre_topc(A_13074)
      | ~ m1_pre_topc(B_13075,'#skF_3'('#skF_5'))
      | v1_tex_2(B_13075,'#skF_3'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71367,c_24])).

tff(c_76919,plain,(
    ! [A_13639] :
      ( m1_pre_topc('#skF_3'('#skF_5'),A_13639)
      | ~ m1_pre_topc('#skF_3'(A_13639),'#skF_3'('#skF_5'))
      | v1_tex_2('#skF_3'(A_13639),'#skF_3'('#skF_5'))
      | ~ l1_pre_topc(A_13639)
      | v2_struct_0(A_13639) ) ),
    inference(resolution,[status(thm)],[c_56,c_72899])).

tff(c_12542,plain,
    ( ~ v1_tex_2('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12502,c_50])).

tff(c_12598,plain,
    ( ~ v1_tex_2('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_12542])).

tff(c_12599,plain,(
    ~ v1_tex_2('#skF_3'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_12598])).

tff(c_76922,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_5')
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76919,c_12599])).

tff(c_76954,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_12605,c_76922])).

tff(c_76955,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_76954])).

tff(c_396,plain,(
    ! [B_122,A_123] :
      ( v2_struct_0(B_122)
      | ~ v7_struct_0(A_123)
      | g1_pre_topc(u1_struct_0(B_122),u1_pre_topc(B_122)) = g1_pre_topc(u1_struct_0(A_123),u1_pre_topc(A_123))
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_289,c_30])).

tff(c_76984,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | ~ v7_struct_0('#skF_5')
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76955,c_396])).

tff(c_77020,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_70120,c_68,c_76984])).

tff(c_77021,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_12496,c_77020])).

tff(c_77139,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_5')
      | v1_tex_2(A_3,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77021,c_383])).

tff(c_77360,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_5')
      | v1_tex_2(A_3,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_77139])).

tff(c_77974,plain,(
    ! [A_13788] :
      ( A_13788 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_13788,'#skF_5')
      | v1_tex_2(A_13788,'#skF_5')
      | ~ v1_pre_topc(A_13788)
      | ~ l1_pre_topc(A_13788) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_77360])).

tff(c_77981,plain,(
    ! [A_13788] :
      ( v2_struct_0(A_13788)
      | ~ l1_pre_topc('#skF_5')
      | ~ v7_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | A_13788 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_13788,'#skF_5')
      | ~ v1_pre_topc(A_13788)
      | ~ l1_pre_topc(A_13788) ) ),
    inference(resolution,[status(thm)],[c_77974,c_30])).

tff(c_77992,plain,(
    ! [A_13788] :
      ( v2_struct_0(A_13788)
      | v2_struct_0('#skF_5')
      | A_13788 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_13788,'#skF_5')
      | ~ v1_pre_topc(A_13788)
      | ~ l1_pre_topc(A_13788) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_84,c_77981])).

tff(c_77999,plain,(
    ! [A_13813] :
      ( v2_struct_0(A_13813)
      | A_13813 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_13813,'#skF_5')
      | ~ v1_pre_topc(A_13813)
      | ~ l1_pre_topc(A_13813) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_77992])).

tff(c_78022,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_77999])).

tff(c_78050,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7765,c_7776,c_78022])).

tff(c_78051,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_10604,c_78050])).

tff(c_10607,plain,
    ( '#skF_3'('#skF_2'('#skF_5')) = '#skF_2'('#skF_5')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6624,c_10604])).

tff(c_10610,plain,(
    '#skF_3'('#skF_2'('#skF_5')) = '#skF_2'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_7776,c_10607])).

tff(c_10656,plain,
    ( m1_pre_topc('#skF_2'('#skF_5'),'#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5'))
    | v2_struct_0('#skF_2'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10610,c_56])).

tff(c_10712,plain,
    ( m1_pre_topc('#skF_2'('#skF_5'),'#skF_2'('#skF_5'))
    | v2_struct_0('#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_10656])).

tff(c_10713,plain,(
    m1_pre_topc('#skF_2'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_10712])).

tff(c_72907,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5'))
    | ~ m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5'))
    | v1_tex_2('#skF_2'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10713,c_72899])).

tff(c_72944,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5'))
    | ~ m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5'))
    | v1_tex_2('#skF_2'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_72907])).

tff(c_72968,plain,(
    ~ m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_72944])).

tff(c_78067,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78051,c_72968])).

tff(c_78089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12605,c_78067])).

tff(c_78091,plain,(
    m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72944])).

tff(c_70167,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_3'('#skF_5'))
      | v1_tex_2(A_3,'#skF_3'('#skF_5'))
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70120,c_383])).

tff(c_70369,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_3'('#skF_5'))
      | v1_tex_2(A_3,'#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_70167])).

tff(c_71991,plain,(
    ! [A_12923] :
      ( A_12923 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_12923,'#skF_3'('#skF_5'))
      | v1_tex_2(A_12923,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_12923)
      | ~ l1_pre_topc(A_12923) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_70369])).

tff(c_72005,plain,(
    ! [A_12923] :
      ( v2_struct_0(A_12923)
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | ~ v7_struct_0('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | A_12923 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_12923,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_12923)
      | ~ l1_pre_topc(A_12923) ) ),
    inference(resolution,[status(thm)],[c_71991,c_30])).

tff(c_72025,plain,(
    ! [A_12923] :
      ( v2_struct_0(A_12923)
      | v2_struct_0('#skF_3'('#skF_5'))
      | A_12923 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_12923,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_12923)
      | ~ l1_pre_topc(A_12923) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70121,c_8063,c_72005])).

tff(c_72026,plain,(
    ! [A_12923] :
      ( v2_struct_0(A_12923)
      | A_12923 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_12923,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_12923)
      | ~ l1_pre_topc(A_12923) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12496,c_72025])).

tff(c_78096,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_78091,c_72026])).

tff(c_78126,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_7776,c_78096])).

tff(c_78127,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_78126])).

tff(c_10635,plain,
    ( v2_struct_0('#skF_3'('#skF_2'('#skF_5')))
    | ~ v7_struct_0('#skF_2'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_2'('#skF_5'))),u1_pre_topc('#skF_2'('#skF_5'))) = '#skF_2'('#skF_5')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5'))
    | v2_struct_0('#skF_2'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10610,c_2965])).

tff(c_10691,plain,
    ( ~ v7_struct_0('#skF_2'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')),u1_pre_topc('#skF_2'('#skF_5'))) = '#skF_2'('#skF_5')
    | v2_struct_0('#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_7776,c_10610,c_10610,c_10635])).

tff(c_10692,plain,
    ( ~ v7_struct_0('#skF_2'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')),u1_pre_topc('#skF_2'('#skF_5'))) = '#skF_2'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_10691])).

tff(c_12093,plain,(
    ~ v7_struct_0('#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10692])).

tff(c_78169,plain,(
    ~ v7_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78127,c_12093])).

tff(c_78182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70121,c_78169])).

tff(c_78183,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')),u1_pre_topc('#skF_2'('#skF_5'))) = '#skF_2'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10692])).

tff(c_78397,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_2'('#skF_5'))
      | v1_tex_2(B_45,'#skF_2'('#skF_5'))
      | ~ l1_pre_topc('#skF_2'('#skF_5'))
      | v2_struct_0('#skF_2'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_78183])).

tff(c_78505,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_2'('#skF_5'))
      | v1_tex_2(B_45,'#skF_2'('#skF_5'))
      | v2_struct_0('#skF_2'('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_78397])).

tff(c_78686,plain,(
    ! [B_13935] :
      ( g1_pre_topc(u1_struct_0(B_13935),u1_pre_topc(B_13935)) = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(B_13935,'#skF_2'('#skF_5'))
      | v1_tex_2(B_13935,'#skF_2'('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_78505])).

tff(c_64,plain,(
    ! [C_56] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_4',C_56)),u1_pre_topc(k1_tex_2('#skF_4',C_56))) != g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_56,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_78850,plain,(
    ! [C_56] :
      ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) != '#skF_2'('#skF_5')
      | ~ m1_subset_1(C_56,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(k1_tex_2('#skF_4',C_56),'#skF_2'('#skF_5'))
      | v1_tex_2(k1_tex_2('#skF_4',C_56),'#skF_2'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78686,c_64])).

tff(c_94811,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) != '#skF_2'('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78850])).

tff(c_94841,plain,(
    ! [A_3] :
      ( A_3 != '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_5')
      | v1_tex_2(A_3,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_94811])).

tff(c_94870,plain,(
    ! [A_3] :
      ( A_3 != '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_5')
      | v1_tex_2(A_3,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_94841])).

tff(c_94992,plain,(
    ! [A_16672] :
      ( A_16672 != '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_16672,'#skF_5')
      | v1_tex_2(A_16672,'#skF_5')
      | ~ v1_pre_topc(A_16672)
      | ~ l1_pre_topc(A_16672) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_94870])).

tff(c_94999,plain,(
    ! [A_16672] :
      ( v2_struct_0(A_16672)
      | ~ l1_pre_topc('#skF_5')
      | ~ v7_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | A_16672 != '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_16672,'#skF_5')
      | ~ v1_pre_topc(A_16672)
      | ~ l1_pre_topc(A_16672) ) ),
    inference(resolution,[status(thm)],[c_94992,c_30])).

tff(c_95010,plain,(
    ! [A_16672] :
      ( v2_struct_0(A_16672)
      | v2_struct_0('#skF_5')
      | A_16672 != '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_16672,'#skF_5')
      | ~ v1_pre_topc(A_16672)
      | ~ l1_pre_topc(A_16672) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_84,c_94999])).

tff(c_95028,plain,(
    ! [A_16721] :
      ( v2_struct_0(A_16721)
      | A_16721 != '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_16721,'#skF_5')
      | ~ v1_pre_topc(A_16721)
      | ~ l1_pre_topc(A_16721) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_95010])).

tff(c_95044,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_95028])).

tff(c_95062,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7765,c_7776,c_95044])).

tff(c_95064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_10604,c_95062])).

tff(c_95066,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_78850])).

tff(c_95337,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_5')
      | v1_tex_2(B_45,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_95066])).

tff(c_95463,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_5')
      | v1_tex_2(B_45,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_95337])).

tff(c_95699,plain,(
    ! [B_16845] :
      ( g1_pre_topc(u1_struct_0(B_16845),u1_pre_topc(B_16845)) = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(B_16845,'#skF_5')
      | v1_tex_2(B_16845,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_95463])).

tff(c_80592,plain,
    ( v2_struct_0('#skF_3'('#skF_3'('#skF_5')))
    | ~ v7_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_3'('#skF_5'))),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80567,c_2965])).

tff(c_80648,plain,
    ( ~ v7_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_80567,c_80567,c_80592])).

tff(c_80649,plain,
    ( ~ v7_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_80648])).

tff(c_80965,plain,(
    ~ v7_struct_0('#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_80649])).

tff(c_85742,plain,(
    ! [A_14974] :
      ( v2_struct_0('#skF_3'(A_14974))
      | ~ v7_struct_0(A_14974)
      | g1_pre_topc(u1_struct_0('#skF_3'(A_14974)),u1_pre_topc('#skF_3'(A_14974))) = g1_pre_topc(u1_struct_0(A_14974),u1_pre_topc(A_14974))
      | ~ l1_pre_topc(A_14974)
      | v2_struct_0(A_14974) ) ),
    inference(resolution,[status(thm)],[c_56,c_6625])).

tff(c_184,plain,(
    ! [B_92,A_93] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_92),u1_pre_topc(B_92)))
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_193,plain,(
    ! [B_23,A_21] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_23),u1_pre_topc(B_23))),u1_pre_topc(g1_pre_topc(u1_struct_0(B_23),u1_pre_topc(B_23)))))
      | ~ m1_pre_topc(B_23,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_24,c_184])).

tff(c_8329,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5')))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8316,c_193])).

tff(c_8361,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5')))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8329])).

tff(c_84070,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5')))),u1_pre_topc('#skF_3'('#skF_5'))))
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8361])).

tff(c_84234,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5')))),u1_pre_topc('#skF_3'('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_84070])).

tff(c_85763,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))),u1_pre_topc('#skF_3'('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5'))
    | ~ v7_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_85742,c_84234])).

tff(c_86129,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))),u1_pre_topc('#skF_3'('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_68,c_85763])).

tff(c_86130,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))),u1_pre_topc('#skF_3'('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80561,c_86129])).

tff(c_86354,plain,(
    ! [B_45] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45))),u1_pre_topc('#skF_3'('#skF_5'))))
      | ~ m1_pre_topc(B_45,'#skF_5')
      | v1_tex_2(B_45,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_86130])).

tff(c_86418,plain,(
    ! [B_45] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45))),u1_pre_topc('#skF_3'('#skF_5'))))
      | ~ m1_pre_topc(B_45,'#skF_5')
      | v1_tex_2(B_45,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86354])).

tff(c_89104,plain,(
    ! [B_15241] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_15241),u1_pre_topc(B_15241))),u1_pre_topc('#skF_3'('#skF_5'))))
      | ~ m1_pre_topc(B_15241,'#skF_5')
      | v1_tex_2(B_15241,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_86418])).

tff(c_89119,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))))
    | ~ m1_pre_topc('#skF_2'('#skF_5'),'#skF_5')
    | v1_tex_2('#skF_2'('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_78183,c_89104])).

tff(c_89319,plain,(
    ~ m1_pre_topc('#skF_2'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_89119])).

tff(c_89322,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_89319])).

tff(c_89325,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_89322])).

tff(c_89327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_89325])).

tff(c_89329,plain,(
    m1_pre_topc('#skF_2'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_89119])).

tff(c_89331,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | ~ v7_struct_0('#skF_5')
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_89329,c_5806])).

tff(c_89363,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_7776,c_84,c_68,c_89331])).

tff(c_89364,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_2'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_10604,c_89363])).

tff(c_89512,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_5')
      | v1_tex_2(A_3,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89364,c_383])).

tff(c_89732,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_5')
      | v1_tex_2(A_3,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_89512])).

tff(c_90257,plain,(
    ! [A_15435] :
      ( A_15435 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_15435,'#skF_5')
      | v1_tex_2(A_15435,'#skF_5')
      | ~ v1_pre_topc(A_15435)
      | ~ l1_pre_topc(A_15435) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_89732])).

tff(c_90268,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90257,c_50])).

tff(c_90279,plain,
    ( v2_struct_0('#skF_5')
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_84,c_90268])).

tff(c_90280,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_90279])).

tff(c_90313,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_90280])).

tff(c_90316,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_90313])).

tff(c_90319,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_90316])).

tff(c_90321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_90319])).

tff(c_90322,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_90280])).

tff(c_81567,plain,(
    ! [A_14358,B_14359] :
      ( m1_pre_topc('#skF_2'('#skF_5'),A_14358)
      | ~ m1_pre_topc(B_14359,A_14358)
      | ~ l1_pre_topc(A_14358)
      | ~ m1_pre_topc(B_14359,'#skF_2'('#skF_5'))
      | v1_tex_2(B_14359,'#skF_2'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78686,c_24])).

tff(c_81571,plain,
    ( m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5'))
    | v1_tex_2('#skF_3'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_80670,c_81567])).

tff(c_81605,plain,
    ( m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5'))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5'))
    | v1_tex_2('#skF_3'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_81571])).

tff(c_81636,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_81605])).

tff(c_90339,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90322,c_81636])).

tff(c_90362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80670,c_90339])).

tff(c_90364,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_81605])).

tff(c_78184,plain,(
    v7_struct_0('#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_10692])).

tff(c_78221,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_2'('#skF_5'))
      | v1_tex_2(A_3,'#skF_2'('#skF_5'))
      | ~ l1_pre_topc('#skF_2'('#skF_5'))
      | v2_struct_0('#skF_2'('#skF_5'))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78183,c_383])).

tff(c_78422,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_2'('#skF_5'))
      | v1_tex_2(A_3,'#skF_2'('#skF_5'))
      | v2_struct_0('#skF_2'('#skF_5'))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_78221])).

tff(c_79055,plain,(
    ! [A_13960] :
      ( A_13960 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_13960,'#skF_2'('#skF_5'))
      | v1_tex_2(A_13960,'#skF_2'('#skF_5'))
      | ~ v1_pre_topc(A_13960)
      | ~ l1_pre_topc(A_13960) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_78422])).

tff(c_79069,plain,(
    ! [A_13960] :
      ( v2_struct_0(A_13960)
      | ~ l1_pre_topc('#skF_2'('#skF_5'))
      | ~ v7_struct_0('#skF_2'('#skF_5'))
      | v2_struct_0('#skF_2'('#skF_5'))
      | A_13960 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_13960,'#skF_2'('#skF_5'))
      | ~ v1_pre_topc(A_13960)
      | ~ l1_pre_topc(A_13960) ) ),
    inference(resolution,[status(thm)],[c_79055,c_30])).

tff(c_79089,plain,(
    ! [A_13960] :
      ( v2_struct_0(A_13960)
      | v2_struct_0('#skF_2'('#skF_5'))
      | A_13960 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_13960,'#skF_2'('#skF_5'))
      | ~ v1_pre_topc(A_13960)
      | ~ l1_pre_topc(A_13960) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78184,c_7765,c_79069])).

tff(c_79090,plain,(
    ! [A_13960] :
      ( v2_struct_0(A_13960)
      | A_13960 = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(A_13960,'#skF_2'('#skF_5'))
      | ~ v1_pre_topc(A_13960)
      | ~ l1_pre_topc(A_13960) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_79089])).

tff(c_90369,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90364,c_79090])).

tff(c_90399,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_90369])).

tff(c_90400,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_90399])).

tff(c_90447,plain,(
    v7_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90400,c_78184])).

tff(c_90457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80965,c_90447])).

tff(c_90458,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5') ),
    inference(splitRight,[status(thm)],[c_80649])).

tff(c_95744,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_5')
    | v1_tex_2('#skF_3'('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_95699,c_90458])).

tff(c_96071,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_95744])).

tff(c_96074,plain,
    ( ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_96071])).

tff(c_96077,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_96074])).

tff(c_96079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_96077])).

tff(c_96081,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_95744])).

tff(c_96083,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | ~ v7_struct_0('#skF_5')
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_3'('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_96081,c_5806])).

tff(c_96117,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_84,c_95066,c_68,c_96083])).

tff(c_96118,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80561,c_96117])).

tff(c_90549,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_3'('#skF_5'))
      | v1_tex_2(B_45,'#skF_3'('#skF_5'))
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90458,c_58])).

tff(c_90752,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_3'('#skF_5'))
      | v1_tex_2(B_45,'#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_90549])).

tff(c_91116,plain,(
    ! [B_15679] :
      ( g1_pre_topc(u1_struct_0(B_15679),u1_pre_topc(B_15679)) = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(B_15679,'#skF_3'('#skF_5'))
      | v1_tex_2(B_15679,'#skF_3'('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_90752])).

tff(c_91152,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5'))
    | v1_tex_2('#skF_2'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_91116,c_78183])).

tff(c_91521,plain,(
    ~ m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_91152])).

tff(c_96179,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96118,c_91521])).

tff(c_96199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80670,c_96179])).

tff(c_96201,plain,(
    m1_pre_topc('#skF_2'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_91152])).

tff(c_90459,plain,(
    v7_struct_0('#skF_3'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_80649])).

tff(c_90523,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_3'('#skF_5'))
      | v1_tex_2(A_3,'#skF_3'('#skF_5'))
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90458,c_383])).

tff(c_90741,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_3,'#skF_3'('#skF_5'))
      | v1_tex_2(A_3,'#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_90523])).

tff(c_91019,plain,(
    ! [A_15629] :
      ( A_15629 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_15629,'#skF_3'('#skF_5'))
      | v1_tex_2(A_15629,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_15629)
      | ~ l1_pre_topc(A_15629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_90741])).

tff(c_91033,plain,(
    ! [A_15629] :
      ( v2_struct_0(A_15629)
      | ~ l1_pre_topc('#skF_3'('#skF_5'))
      | ~ v7_struct_0('#skF_3'('#skF_5'))
      | v2_struct_0('#skF_3'('#skF_5'))
      | A_15629 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_15629,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_15629)
      | ~ l1_pre_topc(A_15629) ) ),
    inference(resolution,[status(thm)],[c_91019,c_30])).

tff(c_91053,plain,(
    ! [A_15629] :
      ( v2_struct_0(A_15629)
      | v2_struct_0('#skF_3'('#skF_5'))
      | A_15629 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_15629,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_15629)
      | ~ l1_pre_topc(A_15629) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90459,c_8063,c_91033])).

tff(c_91054,plain,(
    ! [A_15629] :
      ( v2_struct_0(A_15629)
      | A_15629 = '#skF_3'('#skF_5')
      | ~ m1_pre_topc(A_15629,'#skF_3'('#skF_5'))
      | ~ v1_pre_topc(A_15629)
      | ~ l1_pre_topc(A_15629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_91053])).

tff(c_96204,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_96201,c_91054])).

tff(c_96231,plain,
    ( v2_struct_0('#skF_2'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7765,c_7776,c_96204])).

tff(c_96232,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_96231])).

tff(c_78506,plain,(
    ! [B_45] :
      ( g1_pre_topc(u1_struct_0(B_45),u1_pre_topc(B_45)) = '#skF_2'('#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_2'('#skF_5'))
      | v1_tex_2(B_45,'#skF_2'('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10604,c_78505])).

tff(c_90571,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5'))
    | v1_tex_2('#skF_3'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78506,c_90458])).

tff(c_91018,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_90571])).

tff(c_96271,plain,(
    ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96232,c_91018])).

tff(c_96290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80670,c_96271])).

tff(c_96292,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_2'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_90571])).

tff(c_96295,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_96292,c_79090])).

tff(c_96322,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_8243,c_96295])).

tff(c_96323,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_96322])).

tff(c_96424,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_96323,c_18])).

tff(c_96470,plain,
    ( m1_pre_topc('#skF_3'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_96424])).

tff(c_96471,plain,(
    m1_pre_topc('#skF_3'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_96470])).

tff(c_448,plain,(
    ! [B_132,A_9] :
      ( u1_struct_0(B_132) = u1_struct_0(A_9)
      | v1_xboole_0(u1_struct_0(A_9))
      | v1_xboole_0(u1_struct_0(B_132))
      | ~ m1_pre_topc(B_132,A_9)
      | ~ l1_pre_topc(A_9)
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_445])).

tff(c_96497,plain,
    ( u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_96471,c_448])).

tff(c_96535,plain,
    ( u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_84,c_96497])).

tff(c_97574,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_96535])).

tff(c_97577,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_97574])).

tff(c_97581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97577])).

tff(c_97583,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_96535])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_97582,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_96535])).

tff(c_97652,plain,(
    u1_struct_0('#skF_3'('#skF_5')) = u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_97582])).

tff(c_104772,plain,(
    ! [B_19481,A_19482,A_19483] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_19481)),u1_struct_0(A_19482))
      | ~ m1_pre_topc(A_19483,A_19482)
      | ~ l1_pre_topc(A_19482)
      | v2_struct_0(A_19482)
      | ~ m1_pre_topc(B_19481,A_19483)
      | v2_struct_0(B_19481)
      | ~ l1_pre_topc(A_19483)
      | v2_struct_0(A_19483) ) ),
    inference(resolution,[status(thm)],[c_252,c_20])).

tff(c_104808,plain,(
    ! [B_19481] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_19481)),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_19481,'#skF_5')
      | v2_struct_0(B_19481)
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_104772])).

tff(c_104855,plain,(
    ! [B_19481] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_19481)),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_19481,'#skF_5')
      | v2_struct_0(B_19481)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_104808])).

tff(c_104860,plain,(
    ! [B_19508] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_19508)),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_19508,'#skF_5')
      | v2_struct_0(B_19508) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_74,c_104855])).

tff(c_104882,plain,
    ( m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97652,c_104860])).

tff(c_104917,plain,
    ( m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96471,c_104882])).

tff(c_104918,plain,(
    m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_104917])).

tff(c_104925,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104918,c_38])).

tff(c_104944,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_104925])).

tff(c_104945,plain,(
    m1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_104944])).

tff(c_105022,plain,
    ( l1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_104945,c_8])).

tff(c_105077,plain,(
    l1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_105022])).

tff(c_104931,plain,
    ( v1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104918,c_44])).

tff(c_104952,plain,
    ( v1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_104931])).

tff(c_104953,plain,(
    v1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_104952])).

tff(c_97811,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97652,c_10])).

tff(c_97933,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_97811])).

tff(c_97937,plain,(
    ~ l1_struct_0('#skF_3'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_97933])).

tff(c_97940,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_97937])).

tff(c_97944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_97940])).

tff(c_97945,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_97933])).

tff(c_97796,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97652,c_158])).

tff(c_97924,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_97796])).

tff(c_97925,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_97924])).

tff(c_228,plain,(
    ! [A_101,B_102] :
      ( m1_pre_topc(k1_tex_2(A_101,B_102),A_101)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_234,plain,(
    ! [A_105] :
      ( m1_pre_topc(k1_tex_2(A_105,'#skF_1'(u1_struct_0(A_105))),A_105)
      | ~ l1_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_2,c_228])).

tff(c_244,plain,(
    ! [A_105] :
      ( l1_pre_topc(k1_tex_2(A_105,'#skF_1'(u1_struct_0(A_105))))
      | ~ l1_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_234,c_8])).

tff(c_97767,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97652,c_244])).

tff(c_97897,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_97767])).

tff(c_97898,plain,(
    l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_97897])).

tff(c_166,plain,(
    ! [A_87,B_88] :
      ( v1_pre_topc(k1_tex_2(A_87,B_88))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_171,plain,(
    ! [A_87] :
      ( v1_pre_topc(k1_tex_2(A_87,'#skF_1'(u1_struct_0(A_87))))
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_2,c_166])).

tff(c_97790,plain,
    ( v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97652,c_171])).

tff(c_97918,plain,
    ( v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_97790])).

tff(c_97919,plain,(
    v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_97918])).

tff(c_97653,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_3'('#skF_5'))) = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97652,c_90458])).

tff(c_232,plain,(
    ! [A_101] :
      ( m1_pre_topc(k1_tex_2(A_101,'#skF_1'(u1_struct_0(A_101))),A_101)
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_2,c_228])).

tff(c_97770,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97652,c_232])).

tff(c_97900,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_97770])).

tff(c_97901,plain,(
    m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))),'#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_97900])).

tff(c_98300,plain,
    ( v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ v7_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5'))
    | ~ v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_97901,c_5806])).

tff(c_98338,plain,
    ( v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97898,c_97919,c_8063,c_97653,c_97652,c_90459,c_98300])).

tff(c_98339,plain,(
    k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_97925,c_98338])).

tff(c_98411,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'('#skF_5')),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_pre_topc('#skF_3'('#skF_5'),'#skF_3'('#skF_5'))
    | ~ v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_3'('#skF_5')))
    | ~ l1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_98339,c_36])).

tff(c_98445,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0('#skF_5')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_2,c_97652,c_98339,c_8243,c_98339,c_80670,c_97652,c_98339,c_97652,c_98411])).

tff(c_98446,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_98445])).

tff(c_98478,plain,
    ( k1_tarski('#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_98446,c_121])).

tff(c_98493,plain,(
    k1_tarski('#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_97945,c_98478])).

tff(c_104937,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(u1_struct_0('#skF_5'))) = k1_tarski('#skF_1'(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_104918,c_22])).

tff(c_104959,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98493,c_104937])).

tff(c_105467,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_104959])).

tff(c_105470,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_105467,c_10])).

tff(c_105473,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_105470])).

tff(c_105476,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_105473])).

tff(c_105480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_105476])).

tff(c_105481,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_104959])).

tff(c_104934,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104918,c_48])).

tff(c_104956,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_104934])).

tff(c_104957,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_104956])).

tff(c_105009,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ v1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104945,c_36])).

tff(c_105058,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_104918,c_104953,c_105009])).

tff(c_105059,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(u1_struct_0('#skF_5'))) = u1_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_104957,c_105058])).

tff(c_106280,plain,(
    u1_struct_0(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5')))) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105481,c_105059])).

tff(c_106538,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))) = k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5')))
    | ~ v1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_106280,c_4])).

tff(c_106728,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))) = k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105077,c_104953,c_106538])).

tff(c_96488,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | ~ v7_struct_0('#skF_5')
    | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')),u1_pre_topc('#skF_3'('#skF_5'))) = g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_96471,c_396])).

tff(c_96520,plain,
    ( v2_struct_0('#skF_3'('#skF_5'))
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_90458,c_68,c_96488])).

tff(c_96521,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_3'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80561,c_96520])).

tff(c_96560,plain,(
    ! [C_56] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_4',C_56)),u1_pre_topc(k1_tex_2('#skF_4',C_56))) != '#skF_3'('#skF_5')
      | ~ m1_subset_1(C_56,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96521,c_64])).

tff(c_106391,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))) != '#skF_3'('#skF_5')
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106280,c_96560])).

tff(c_106633,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc(k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))))) != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104918,c_106391])).

tff(c_107687,plain,(
    k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))) != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106728,c_106633])).

tff(c_96627,plain,(
    ! [A_21] :
      ( m1_pre_topc('#skF_3'('#skF_5'),A_21)
      | ~ m1_pre_topc('#skF_5',A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96521,c_24])).

tff(c_34,plain,(
    ! [A_30,B_34,C_36] :
      ( k1_tex_2(A_30,B_34) = C_36
      | u1_struct_0(C_36) != k6_domain_1(u1_struct_0(A_30),B_34)
      | ~ m1_pre_topc(C_36,A_30)
      | ~ v1_pre_topc(C_36)
      | v2_struct_0(C_36)
      | ~ m1_subset_1(B_34,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_105786,plain,(
    ! [C_36] :
      ( k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))) = C_36
      | u1_struct_0(C_36) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(C_36,'#skF_4')
      | ~ v1_pre_topc(C_36)
      | v2_struct_0(C_36)
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105481,c_34])).

tff(c_105802,plain,(
    ! [C_36] :
      ( k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))) = C_36
      | u1_struct_0(C_36) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(C_36,'#skF_4')
      | ~ v1_pre_topc(C_36)
      | v2_struct_0(C_36)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_104918,c_105786])).

tff(c_110546,plain,(
    ! [C_21407] :
      ( k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))) = C_21407
      | u1_struct_0(C_21407) != u1_struct_0('#skF_5')
      | ~ m1_pre_topc(C_21407,'#skF_4')
      | ~ v1_pre_topc(C_21407)
      | v2_struct_0(C_21407) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_105802])).

tff(c_110570,plain,
    ( k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))) = '#skF_3'('#skF_5')
    | u1_struct_0('#skF_3'('#skF_5')) != u1_struct_0('#skF_5')
    | ~ v1_pre_topc('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96627,c_110546])).

tff(c_110626,plain,
    ( k1_tex_2('#skF_4','#skF_1'(u1_struct_0('#skF_5'))) = '#skF_3'('#skF_5')
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_8243,c_97652,c_110570])).

tff(c_110628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_107687,c_110626])).

tff(c_110629,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_97582])).

tff(c_110631,plain,(
    v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_110629])).

tff(c_110634,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_110631,c_10])).

tff(c_110637,plain,(
    ~ l1_struct_0('#skF_3'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80561,c_110634])).

tff(c_110640,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_110637])).

tff(c_110644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_110640])).

tff(c_110645,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_110629])).

tff(c_110649,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_110645,c_10])).

tff(c_110652,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97583,c_110649])).

tff(c_110654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.10/16.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.36/17.06  
% 28.36/17.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.36/17.06  %$ v1_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3
% 28.36/17.06  
% 28.36/17.06  %Foreground sorts:
% 28.36/17.06  
% 28.36/17.06  
% 28.36/17.06  %Background operators:
% 28.36/17.06  
% 28.36/17.06  
% 28.36/17.06  %Foreground operators:
% 28.36/17.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 28.36/17.06  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 28.36/17.06  tff('#skF_2', type, '#skF_2': $i > $i).
% 28.36/17.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.36/17.06  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 28.36/17.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 28.36/17.06  tff('#skF_1', type, '#skF_1': $i > $i).
% 28.36/17.06  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 28.36/17.06  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 28.36/17.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 28.36/17.06  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 28.36/17.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.36/17.06  tff('#skF_5', type, '#skF_5': $i).
% 28.36/17.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 28.36/17.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 28.36/17.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.36/17.06  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 28.36/17.06  tff('#skF_4', type, '#skF_4': $i).
% 28.36/17.06  tff('#skF_3', type, '#skF_3': $i > $i).
% 28.36/17.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.36/17.06  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 28.36/17.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 28.36/17.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 28.36/17.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.36/17.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.36/17.06  
% 28.75/17.12  tff(f_252, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v7_struct_0(B)) & m1_pre_topc(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A, C)), u1_pre_topc(k1_tex_2(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tex_2)).
% 28.75/17.12  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 28.75/17.12  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 28.75/17.12  tff(f_194, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (?[B]: (((m1_pre_topc(B, A) & ~v2_struct_0(B)) & v1_pre_topc(B)) & ~v1_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_tex_2)).
% 28.75/17.12  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 28.75/17.12  tff(f_207, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_tex_2(B, A) & m1_pre_topc(B, A)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tex_2)).
% 28.75/17.12  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 28.75/17.12  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 28.75/17.12  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (?[B]: ((m1_pre_topc(B, A) & ~v2_struct_0(B)) & v1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_pre_topc)).
% 28.75/17.12  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 28.75/17.12  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 28.75/17.12  tff(f_220, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 28.75/17.12  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 28.75/17.12  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 28.75/17.12  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 28.75/17.12  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 28.75/17.12  tff(f_178, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 28.75/17.12  tff(f_164, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 28.75/17.12  tff(f_150, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 28.75/17.12  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_252])).
% 28.75/17.12  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 28.75/17.12  tff(c_66, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 28.75/17.12  tff(c_78, plain, (![B_60, A_61]: (l1_pre_topc(B_60) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 28.75/17.12  tff(c_81, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_78])).
% 28.75/17.12  tff(c_84, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_81])).
% 28.75/17.12  tff(c_6, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 28.75/17.12  tff(c_68, plain, (v7_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_252])).
% 28.75/17.12  tff(c_91, plain, (![A_68]: (m1_pre_topc('#skF_3'(A_68), A_68) | ~l1_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_194])).
% 28.75/17.12  tff(c_8, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 28.75/17.12  tff(c_95, plain, (![A_68]: (l1_pre_topc('#skF_3'(A_68)) | ~l1_pre_topc(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_91, c_8])).
% 28.75/17.12  tff(c_56, plain, (![A_41]: (m1_pre_topc('#skF_3'(A_41), A_41) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_194])).
% 28.75/17.12  tff(c_4, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.75/17.12  tff(c_289, plain, (![B_122, A_123]: (g1_pre_topc(u1_struct_0(B_122), u1_pre_topc(B_122))=g1_pre_topc(u1_struct_0(A_123), u1_pre_topc(A_123)) | ~m1_pre_topc(B_122, A_123) | v1_tex_2(B_122, A_123) | ~l1_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_207])).
% 28.75/17.12  tff(c_24, plain, (![B_23, A_21]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_23), u1_pre_topc(B_23)), A_21) | ~m1_pre_topc(B_23, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 28.75/17.12  tff(c_7438, plain, (![B_2515, A_2516, A_2517]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_2515), u1_pre_topc(B_2515)), A_2516) | ~m1_pre_topc(A_2517, A_2516) | ~l1_pre_topc(A_2516) | ~m1_pre_topc(B_2515, A_2517) | v1_tex_2(B_2515, A_2517) | ~l1_pre_topc(A_2517) | v2_struct_0(A_2517))), inference(superposition, [status(thm), theory('equality')], [c_289, c_24])).
% 28.75/17.12  tff(c_7472, plain, (![B_2515]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_2515), u1_pre_topc(B_2515)), '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_2515, '#skF_5') | v1_tex_2(B_2515, '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_7438])).
% 28.75/17.12  tff(c_7480, plain, (![B_2515]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_2515), u1_pre_topc(B_2515)), '#skF_4') | ~m1_pre_topc(B_2515, '#skF_5') | v1_tex_2(B_2515, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_72, c_7472])).
% 28.75/17.12  tff(c_7482, plain, (![B_2542]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_2542), u1_pre_topc(B_2542)), '#skF_4') | ~m1_pre_topc(B_2542, '#skF_5') | v1_tex_2(B_2542, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_7480])).
% 28.75/17.12  tff(c_7691, plain, (![A_2567]: (m1_pre_topc(A_2567, '#skF_4') | ~m1_pre_topc(A_2567, '#skF_5') | v1_tex_2(A_2567, '#skF_5') | ~v1_pre_topc(A_2567) | ~l1_pre_topc(A_2567))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7482])).
% 28.75/17.12  tff(c_30, plain, (![B_29, A_27]: (~v1_tex_2(B_29, A_27) | v2_struct_0(B_29) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27) | ~v7_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_130])).
% 28.75/17.12  tff(c_7698, plain, (![A_2567]: (v2_struct_0(A_2567) | ~l1_pre_topc('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5') | m1_pre_topc(A_2567, '#skF_4') | ~m1_pre_topc(A_2567, '#skF_5') | ~v1_pre_topc(A_2567) | ~l1_pre_topc(A_2567))), inference(resolution, [status(thm)], [c_7691, c_30])).
% 28.75/17.12  tff(c_7709, plain, (![A_2567]: (v2_struct_0(A_2567) | v2_struct_0('#skF_5') | m1_pre_topc(A_2567, '#skF_4') | ~m1_pre_topc(A_2567, '#skF_5') | ~v1_pre_topc(A_2567) | ~l1_pre_topc(A_2567))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_84, c_7698])).
% 28.75/17.12  tff(c_7715, plain, (![A_2592]: (v2_struct_0(A_2592) | m1_pre_topc(A_2592, '#skF_4') | ~m1_pre_topc(A_2592, '#skF_5') | ~v1_pre_topc(A_2592) | ~l1_pre_topc(A_2592))), inference(negUnitSimplification, [status(thm)], [c_70, c_7709])).
% 28.75/17.12  tff(c_7735, plain, (v2_struct_0('#skF_3'('#skF_5')) | m1_pre_topc('#skF_3'('#skF_5'), '#skF_4') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_7715])).
% 28.75/17.12  tff(c_7753, plain, (v2_struct_0('#skF_3'('#skF_5')) | m1_pre_topc('#skF_3'('#skF_5'), '#skF_4') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7735])).
% 28.75/17.12  tff(c_7754, plain, (v2_struct_0('#skF_3'('#skF_5')) | m1_pre_topc('#skF_3'('#skF_5'), '#skF_4') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_7753])).
% 28.75/17.12  tff(c_8053, plain, (~l1_pre_topc('#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_7754])).
% 28.75/17.12  tff(c_8056, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_95, c_8053])).
% 28.75/17.12  tff(c_8059, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_8056])).
% 28.75/17.12  tff(c_8061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_8059])).
% 28.75/17.12  tff(c_8063, plain, (l1_pre_topc('#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_7754])).
% 28.75/17.12  tff(c_58, plain, (![B_45, A_43]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))=g1_pre_topc(u1_struct_0(A_43), u1_pre_topc(A_43)) | ~m1_pre_topc(B_45, A_43) | v1_tex_2(B_45, A_43) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_207])).
% 28.75/17.12  tff(c_52, plain, (![A_41]: (v1_pre_topc('#skF_3'(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_194])).
% 28.75/17.12  tff(c_8062, plain, (~v1_pre_topc('#skF_3'('#skF_5')) | m1_pre_topc('#skF_3'('#skF_5'), '#skF_4') | v2_struct_0('#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_7754])).
% 28.75/17.12  tff(c_8233, plain, (~v1_pre_topc('#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_8062])).
% 28.75/17.12  tff(c_8236, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_8233])).
% 28.75/17.12  tff(c_8239, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_8236])).
% 28.75/17.12  tff(c_8241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_8239])).
% 28.75/17.12  tff(c_8242, plain, (v2_struct_0('#skF_3'('#skF_5')) | m1_pre_topc('#skF_3'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_8062])).
% 28.75/17.12  tff(c_8316, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_8242])).
% 28.75/17.12  tff(c_26, plain, (![B_23, A_21]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_23), u1_pre_topc(B_23))) | ~m1_pre_topc(B_23, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 28.75/17.12  tff(c_8337, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8316, c_26])).
% 28.75/17.12  tff(c_8373, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8337])).
% 28.75/17.12  tff(c_8679, plain, (![B_45]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))) | ~m1_pre_topc(B_45, '#skF_3'('#skF_5')) | v1_tex_2(B_45, '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_8373])).
% 28.75/17.12  tff(c_8724, plain, (![B_45]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))) | ~m1_pre_topc(B_45, '#skF_3'('#skF_5')) | v1_tex_2(B_45, '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8679])).
% 28.75/17.12  tff(c_80551, plain, (v2_struct_0('#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_8724])).
% 28.75/17.12  tff(c_54, plain, (![A_41]: (~v2_struct_0('#skF_3'(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_194])).
% 28.75/17.12  tff(c_80554, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_80551, c_54])).
% 28.75/17.12  tff(c_80557, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80554])).
% 28.75/17.12  tff(c_80559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_80557])).
% 28.75/17.12  tff(c_80561, plain, (~v2_struct_0('#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_8724])).
% 28.75/17.12  tff(c_8243, plain, (v1_pre_topc('#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_8062])).
% 28.75/17.12  tff(c_3102, plain, (![A_1125, A_1126]: (g1_pre_topc(u1_struct_0(A_1125), u1_pre_topc(A_1125))=A_1126 | ~m1_pre_topc(A_1126, A_1125) | v1_tex_2(A_1126, A_1125) | ~l1_pre_topc(A_1125) | v2_struct_0(A_1125) | ~v1_pre_topc(A_1126) | ~l1_pre_topc(A_1126))), inference(superposition, [status(thm), theory('equality')], [c_4, c_289])).
% 28.75/17.12  tff(c_6549, plain, (![A_2138, A_2137]: (A_2138=A_2137 | ~m1_pre_topc(A_2138, A_2137) | v1_tex_2(A_2138, A_2137) | ~l1_pre_topc(A_2137) | v2_struct_0(A_2137) | ~v1_pre_topc(A_2138) | ~l1_pre_topc(A_2138) | ~v1_pre_topc(A_2137) | ~l1_pre_topc(A_2137))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3102])).
% 28.75/17.12  tff(c_50, plain, (![A_41]: (~v1_tex_2('#skF_3'(A_41), A_41) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_194])).
% 28.75/17.12  tff(c_6592, plain, (![A_2189]: ('#skF_3'(A_2189)=A_2189 | ~m1_pre_topc('#skF_3'(A_2189), A_2189) | v2_struct_0(A_2189) | ~v1_pre_topc('#skF_3'(A_2189)) | ~l1_pre_topc('#skF_3'(A_2189)) | ~v1_pre_topc(A_2189) | ~l1_pre_topc(A_2189))), inference(resolution, [status(thm)], [c_6549, c_50])).
% 28.75/17.12  tff(c_6603, plain, (![A_2214]: ('#skF_3'(A_2214)=A_2214 | ~v1_pre_topc('#skF_3'(A_2214)) | ~l1_pre_topc('#skF_3'(A_2214)) | ~v1_pre_topc(A_2214) | ~l1_pre_topc(A_2214) | v2_struct_0(A_2214))), inference(resolution, [status(thm)], [c_56, c_6592])).
% 28.75/17.12  tff(c_6614, plain, (![A_2239]: ('#skF_3'(A_2239)=A_2239 | ~l1_pre_topc('#skF_3'(A_2239)) | ~v1_pre_topc(A_2239) | ~l1_pre_topc(A_2239) | v2_struct_0(A_2239))), inference(resolution, [status(thm)], [c_52, c_6603])).
% 28.75/17.12  tff(c_6624, plain, (![A_68]: ('#skF_3'(A_68)=A_68 | ~v1_pre_topc(A_68) | ~l1_pre_topc(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_95, c_6614])).
% 28.75/17.12  tff(c_80564, plain, ('#skF_3'('#skF_3'('#skF_5'))='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_6624, c_80561])).
% 28.75/17.12  tff(c_80567, plain, ('#skF_3'('#skF_3'('#skF_5'))='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_80564])).
% 28.75/17.12  tff(c_80613, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_80567, c_56])).
% 28.75/17.12  tff(c_80669, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_80613])).
% 28.75/17.12  tff(c_80670, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80561, c_80669])).
% 28.75/17.12  tff(c_98, plain, (![A_71]: (m1_pre_topc('#skF_2'(A_71), A_71) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.75/17.12  tff(c_102, plain, (![A_71]: (l1_pre_topc('#skF_2'(A_71)) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(resolution, [status(thm)], [c_98, c_8])).
% 28.75/17.12  tff(c_18, plain, (![A_10]: (m1_pre_topc('#skF_2'(A_10), A_10) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.75/17.12  tff(c_7731, plain, (v2_struct_0('#skF_2'('#skF_5')) | m1_pre_topc('#skF_2'('#skF_5'), '#skF_4') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_7715])).
% 28.75/17.12  tff(c_7749, plain, (v2_struct_0('#skF_2'('#skF_5')) | m1_pre_topc('#skF_2'('#skF_5'), '#skF_4') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7731])).
% 28.75/17.12  tff(c_7750, plain, (v2_struct_0('#skF_2'('#skF_5')) | m1_pre_topc('#skF_2'('#skF_5'), '#skF_4') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_7749])).
% 28.75/17.12  tff(c_7755, plain, (~l1_pre_topc('#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_7750])).
% 28.75/17.12  tff(c_7758, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_102, c_7755])).
% 28.75/17.12  tff(c_7761, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7758])).
% 28.75/17.12  tff(c_7763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_7761])).
% 28.75/17.12  tff(c_7765, plain, (l1_pre_topc('#skF_2'('#skF_5'))), inference(splitRight, [status(thm)], [c_7750])).
% 28.75/17.12  tff(c_14, plain, (![A_10]: (v1_pre_topc('#skF_2'(A_10)) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.75/17.12  tff(c_7764, plain, (~v1_pre_topc('#skF_2'('#skF_5')) | m1_pre_topc('#skF_2'('#skF_5'), '#skF_4') | v2_struct_0('#skF_2'('#skF_5'))), inference(splitRight, [status(thm)], [c_7750])).
% 28.75/17.12  tff(c_7766, plain, (~v1_pre_topc('#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_7764])).
% 28.75/17.12  tff(c_7769, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_14, c_7766])).
% 28.75/17.12  tff(c_7772, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7769])).
% 28.75/17.12  tff(c_7774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_7772])).
% 28.75/17.12  tff(c_7775, plain, (v2_struct_0('#skF_2'('#skF_5')) | m1_pre_topc('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_7764])).
% 28.75/17.12  tff(c_7825, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_7775])).
% 28.75/17.12  tff(c_173, plain, (![B_90, A_91]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_90), u1_pre_topc(B_90)), A_91) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_104])).
% 28.75/17.12  tff(c_183, plain, (![B_90, A_91]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_90), u1_pre_topc(B_90))) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_173, c_8])).
% 28.75/17.12  tff(c_7844, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')), u1_pre_topc('#skF_2'('#skF_5')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_7825, c_183])).
% 28.75/17.12  tff(c_7879, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')), u1_pre_topc('#skF_2'('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7844])).
% 28.75/17.12  tff(c_8007, plain, (![B_45]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))) | ~m1_pre_topc(B_45, '#skF_2'('#skF_5')) | v1_tex_2(B_45, '#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_7879])).
% 28.75/17.12  tff(c_8050, plain, (![B_45]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))) | ~m1_pre_topc(B_45, '#skF_2'('#skF_5')) | v1_tex_2(B_45, '#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_8007])).
% 28.75/17.12  tff(c_9885, plain, (v2_struct_0('#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_8050])).
% 28.75/17.12  tff(c_16, plain, (![A_10]: (~v2_struct_0('#skF_2'(A_10)) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.75/17.12  tff(c_10597, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_9885, c_16])).
% 28.75/17.12  tff(c_10600, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_10597])).
% 28.75/17.12  tff(c_10602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_10600])).
% 28.75/17.12  tff(c_10604, plain, (~v2_struct_0('#skF_2'('#skF_5'))), inference(splitRight, [status(thm)], [c_8050])).
% 28.75/17.12  tff(c_7776, plain, (v1_pre_topc('#skF_2'('#skF_5'))), inference(splitRight, [status(thm)], [c_7764])).
% 28.75/17.12  tff(c_383, plain, (![A_123, A_3]: (g1_pre_topc(u1_struct_0(A_123), u1_pre_topc(A_123))=A_3 | ~m1_pre_topc(A_3, A_123) | v1_tex_2(A_3, A_123) | ~l1_pre_topc(A_123) | v2_struct_0(A_123) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_289])).
% 28.75/17.12  tff(c_12, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 28.75/17.12  tff(c_28, plain, (![B_26, A_24]: (r1_tarski(u1_struct_0(B_26), u1_struct_0(A_24)) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.75/17.12  tff(c_131, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(A_80, B_79) | ~v1_zfmisc_1(B_79) | v1_xboole_0(B_79) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_220])).
% 28.75/17.12  tff(c_445, plain, (![B_132, A_133]: (u1_struct_0(B_132)=u1_struct_0(A_133) | ~v1_zfmisc_1(u1_struct_0(A_133)) | v1_xboole_0(u1_struct_0(A_133)) | v1_xboole_0(u1_struct_0(B_132)) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_28, c_131])).
% 28.75/17.12  tff(c_537, plain, (![B_141, A_142]: (u1_struct_0(B_141)=u1_struct_0(A_142) | v1_xboole_0(u1_struct_0(A_142)) | v1_xboole_0(u1_struct_0(B_141)) | ~m1_pre_topc(B_141, A_142) | ~l1_pre_topc(A_142) | ~l1_struct_0(A_142) | ~v7_struct_0(A_142))), inference(resolution, [status(thm)], [c_12, c_445])).
% 28.75/17.12  tff(c_554, plain, (![A_41]: (u1_struct_0('#skF_3'(A_41))=u1_struct_0(A_41) | v1_xboole_0(u1_struct_0(A_41)) | v1_xboole_0(u1_struct_0('#skF_3'(A_41))) | ~l1_struct_0(A_41) | ~v7_struct_0(A_41) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_56, c_537])).
% 28.75/17.12  tff(c_12486, plain, (v2_struct_0('#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_8724])).
% 28.75/17.12  tff(c_12489, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_12486, c_54])).
% 28.75/17.12  tff(c_12492, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_12489])).
% 28.75/17.12  tff(c_12494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_12492])).
% 28.75/17.12  tff(c_12496, plain, (~v2_struct_0('#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_8724])).
% 28.75/17.12  tff(c_12499, plain, ('#skF_3'('#skF_3'('#skF_5'))='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_6624, c_12496])).
% 28.75/17.12  tff(c_12502, plain, ('#skF_3'('#skF_3'('#skF_5'))='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_12499])).
% 28.75/17.12  tff(c_12548, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12502, c_56])).
% 28.75/17.12  tff(c_12604, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_12548])).
% 28.75/17.12  tff(c_12605, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_12496, c_12604])).
% 28.75/17.12  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 28.75/17.12  tff(c_247, plain, (![C_109, A_110, B_111]: (m1_subset_1(C_109, u1_struct_0(A_110)) | ~m1_subset_1(C_109, u1_struct_0(B_111)) | ~m1_pre_topc(B_111, A_110) | v2_struct_0(B_111) | ~l1_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_88])).
% 28.75/17.12  tff(c_252, plain, (![B_112, A_113]: (m1_subset_1('#skF_1'(u1_struct_0(B_112)), u1_struct_0(A_113)) | ~m1_pre_topc(B_112, A_113) | v2_struct_0(B_112) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_2, c_247])).
% 28.75/17.12  tff(c_20, plain, (![C_18, A_12, B_16]: (m1_subset_1(C_18, u1_struct_0(A_12)) | ~m1_subset_1(C_18, u1_struct_0(B_16)) | ~m1_pre_topc(B_16, A_12) | v2_struct_0(B_16) | ~l1_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_88])).
% 28.75/17.12  tff(c_43297, plain, (![B_6857, A_6858, A_6859]: (m1_subset_1('#skF_1'(u1_struct_0(B_6857)), u1_struct_0(A_6858)) | ~m1_pre_topc(A_6859, A_6858) | ~l1_pre_topc(A_6858) | v2_struct_0(A_6858) | ~m1_pre_topc(B_6857, A_6859) | v2_struct_0(B_6857) | ~l1_pre_topc(A_6859) | v2_struct_0(A_6859))), inference(resolution, [status(thm)], [c_252, c_20])).
% 28.75/17.12  tff(c_43311, plain, (![B_6857]: (m1_subset_1('#skF_1'(u1_struct_0(B_6857)), u1_struct_0('#skF_3'('#skF_5'))) | ~m1_pre_topc(B_6857, '#skF_3'('#skF_5')) | v2_struct_0(B_6857) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')))), inference(resolution, [status(thm)], [c_12605, c_43297])).
% 28.75/17.12  tff(c_43363, plain, (![B_6857]: (m1_subset_1('#skF_1'(u1_struct_0(B_6857)), u1_struct_0('#skF_3'('#skF_5'))) | ~m1_pre_topc(B_6857, '#skF_3'('#skF_5')) | v2_struct_0(B_6857) | v2_struct_0('#skF_3'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_43311])).
% 28.75/17.12  tff(c_44962, plain, (![B_7410]: (m1_subset_1('#skF_1'(u1_struct_0(B_7410)), u1_struct_0('#skF_3'('#skF_5'))) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(negUnitSimplification, [status(thm)], [c_12496, c_43363])).
% 28.75/17.12  tff(c_22, plain, (![A_19, B_20]: (k6_domain_1(A_19, B_20)=k1_tarski(B_20) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_95])).
% 28.75/17.12  tff(c_45010, plain, (![B_7410]: (k6_domain_1(u1_struct_0('#skF_3'('#skF_5')), '#skF_1'(u1_struct_0(B_7410)))=k1_tarski('#skF_1'(u1_struct_0(B_7410))) | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(resolution, [status(thm)], [c_44962, c_22])).
% 28.75/17.12  tff(c_58581, plain, (v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))), inference(splitLeft, [status(thm)], [c_45010])).
% 28.75/17.12  tff(c_10, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 28.75/17.12  tff(c_58584, plain, (~l1_struct_0('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_58581, c_10])).
% 28.75/17.12  tff(c_58587, plain, (~l1_struct_0('#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_12496, c_58584])).
% 28.75/17.12  tff(c_58590, plain, (~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_58587])).
% 28.75/17.12  tff(c_58594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8063, c_58590])).
% 28.75/17.12  tff(c_58596, plain, (~v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))), inference(splitRight, [status(thm)], [c_45010])).
% 28.75/17.12  tff(c_58599, plain, (u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | ~v7_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_554, c_58596])).
% 28.75/17.12  tff(c_58602, plain, (u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_68, c_58599])).
% 28.75/17.12  tff(c_58603, plain, (u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_58602])).
% 28.75/17.12  tff(c_58604, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_58603])).
% 28.75/17.12  tff(c_58607, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_58604])).
% 28.75/17.12  tff(c_58611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_58607])).
% 28.75/17.12  tff(c_58613, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_58603])).
% 28.75/17.12  tff(c_661, plain, (![B_146, A_147]: (g1_pre_topc(u1_struct_0(B_146), u1_pre_topc(B_146))=A_147 | ~m1_pre_topc(B_146, A_147) | v1_tex_2(B_146, A_147) | ~l1_pre_topc(A_147) | v2_struct_0(A_147) | ~v1_pre_topc(A_147) | ~l1_pre_topc(A_147))), inference(superposition, [status(thm), theory('equality')], [c_4, c_289])).
% 28.75/17.12  tff(c_2937, plain, (![B_1098, A_1099]: (v2_struct_0(B_1098) | ~v7_struct_0(A_1099) | g1_pre_topc(u1_struct_0(B_1098), u1_pre_topc(B_1098))=A_1099 | ~m1_pre_topc(B_1098, A_1099) | v2_struct_0(A_1099) | ~v1_pre_topc(A_1099) | ~l1_pre_topc(A_1099))), inference(resolution, [status(thm)], [c_661, c_30])).
% 28.75/17.12  tff(c_2965, plain, (![A_41]: (v2_struct_0('#skF_3'(A_41)) | ~v7_struct_0(A_41) | g1_pre_topc(u1_struct_0('#skF_3'(A_41)), u1_pre_topc('#skF_3'(A_41)))=A_41 | ~v1_pre_topc(A_41) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_56, c_2937])).
% 28.75/17.12  tff(c_12527, plain, (v2_struct_0('#skF_3'('#skF_3'('#skF_5'))) | ~v7_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_3'('#skF_5'))), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12502, c_2965])).
% 28.75/17.12  tff(c_12583, plain, (~v7_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5') | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_12502, c_12502, c_12527])).
% 28.75/17.12  tff(c_12584, plain, (~v7_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_12496, c_12583])).
% 28.75/17.12  tff(c_12698, plain, (~v7_struct_0('#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_12584])).
% 28.75/17.12  tff(c_58612, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_58603])).
% 28.75/17.12  tff(c_58614, plain, (u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_58612])).
% 28.75/17.12  tff(c_153, plain, (![A_83, B_84]: (~v2_struct_0(k1_tex_2(A_83, B_84)) | ~m1_subset_1(B_84, u1_struct_0(A_83)) | ~l1_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_178])).
% 28.75/17.12  tff(c_158, plain, (![A_83]: (~v2_struct_0(k1_tex_2(A_83, '#skF_1'(u1_struct_0(A_83)))) | ~l1_pre_topc(A_83) | v2_struct_0(A_83))), inference(resolution, [status(thm)], [c_2, c_153])).
% 28.75/17.12  tff(c_59291, plain, (~v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58614, c_158])).
% 28.75/17.12  tff(c_59741, plain, (~v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_59291])).
% 28.75/17.12  tff(c_59742, plain, (~v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_12496, c_59741])).
% 28.75/17.12  tff(c_38, plain, (![A_37, B_38]: (m1_pre_topc(k1_tex_2(A_37, B_38), A_37) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_164])).
% 28.75/17.12  tff(c_44966, plain, (![B_7410]: (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0(B_7410))), '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(resolution, [status(thm)], [c_44962, c_38])).
% 28.75/17.12  tff(c_44996, plain, (![B_7410]: (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0(B_7410))), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_44966])).
% 28.75/17.12  tff(c_44997, plain, (![B_7410]: (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0(B_7410))), '#skF_3'('#skF_5')) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(negUnitSimplification, [status(thm)], [c_12496, c_44996])).
% 28.75/17.12  tff(c_58863, plain, (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58614, c_44997])).
% 28.75/17.12  tff(c_59470, plain, (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12605, c_58863])).
% 28.75/17.12  tff(c_59471, plain, (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_12496, c_59470])).
% 28.75/17.12  tff(c_58615, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58614, c_58596])).
% 28.75/17.12  tff(c_43364, plain, (![B_6857]: (m1_subset_1('#skF_1'(u1_struct_0(B_6857)), u1_struct_0('#skF_3'('#skF_5'))) | ~m1_pre_topc(B_6857, '#skF_3'('#skF_5')) | v2_struct_0(B_6857))), inference(negUnitSimplification, [status(thm)], [c_12496, c_43363])).
% 28.75/17.12  tff(c_64036, plain, (![B_11085]: (m1_subset_1('#skF_1'(u1_struct_0(B_11085)), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(demodulation, [status(thm), theory('equality')], [c_58614, c_43364])).
% 28.75/17.12  tff(c_48, plain, (![A_39, B_40]: (~v2_struct_0(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_178])).
% 28.75/17.12  tff(c_64052, plain, (![B_11085]: (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(resolution, [status(thm)], [c_64036, c_48])).
% 28.75/17.12  tff(c_64092, plain, (![B_11085]: (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64052])).
% 28.75/17.12  tff(c_64146, plain, (![B_11159]: (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11159)))) | ~m1_pre_topc(B_11159, '#skF_3'('#skF_5')) | v2_struct_0(B_11159))), inference(negUnitSimplification, [status(thm)], [c_70, c_64092])).
% 28.75/17.12  tff(c_64152, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58614, c_64146])).
% 28.75/17.12  tff(c_64176, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12605, c_64152])).
% 28.75/17.12  tff(c_64177, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_12496, c_64176])).
% 28.75/17.12  tff(c_44, plain, (![A_39, B_40]: (v1_pre_topc(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_178])).
% 28.75/17.12  tff(c_64049, plain, (![B_11085]: (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(resolution, [status(thm)], [c_64036, c_44])).
% 28.75/17.12  tff(c_64088, plain, (![B_11085]: (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64049])).
% 28.75/17.12  tff(c_64190, plain, (![B_11208]: (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11208)))) | ~m1_pre_topc(B_11208, '#skF_3'('#skF_5')) | v2_struct_0(B_11208))), inference(negUnitSimplification, [status(thm)], [c_70, c_64088])).
% 28.75/17.12  tff(c_64196, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58614, c_64190])).
% 28.75/17.12  tff(c_64217, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12605, c_64196])).
% 28.75/17.12  tff(c_64218, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_12496, c_64217])).
% 28.75/17.12  tff(c_64043, plain, (![B_11085]: (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085))), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(resolution, [status(thm)], [c_64036, c_38])).
% 28.75/17.12  tff(c_64080, plain, (![B_11085]: (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085))), '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64043])).
% 28.75/17.12  tff(c_65372, plain, (![B_11526]: (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11526))), '#skF_5') | ~m1_pre_topc(B_11526, '#skF_3'('#skF_5')) | v2_struct_0(B_11526))), inference(negUnitSimplification, [status(thm)], [c_70, c_64080])).
% 28.75/17.12  tff(c_65424, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_5') | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58614, c_65372])).
% 28.75/17.12  tff(c_65510, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_5') | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12605, c_65424])).
% 28.75/17.12  tff(c_65511, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_12496, c_65510])).
% 28.75/17.12  tff(c_36, plain, (![A_30, B_34]: (k6_domain_1(u1_struct_0(A_30), B_34)=u1_struct_0(k1_tex_2(A_30, B_34)) | ~m1_pre_topc(k1_tex_2(A_30, B_34), A_30) | ~v1_pre_topc(k1_tex_2(A_30, B_34)) | v2_struct_0(k1_tex_2(A_30, B_34)) | ~m1_subset_1(B_34, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_150])).
% 28.75/17.12  tff(c_65544, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | ~v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_65511, c_36])).
% 28.75/17.12  tff(c_65620, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2, c_64218, c_65544])).
% 28.75/17.12  tff(c_65621, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_64177, c_65620])).
% 28.75/17.12  tff(c_117, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_95])).
% 28.75/17.12  tff(c_121, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2, c_117])).
% 28.75/17.12  tff(c_65695, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))))=k1_tarski('#skF_1'(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_65621, c_121])).
% 28.75/17.12  tff(c_65716, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5'))))=k1_tarski('#skF_1'(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58615, c_65695])).
% 28.75/17.12  tff(c_65724, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))=k1_tarski('#skF_1'(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_65716, c_65621])).
% 28.75/17.12  tff(c_44972, plain, (![B_7410]: (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0(B_7410)))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(resolution, [status(thm)], [c_44962, c_44])).
% 28.75/17.12  tff(c_45004, plain, (![B_7410]: (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0(B_7410)))) | v2_struct_0('#skF_3'('#skF_5')) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_44972])).
% 28.75/17.12  tff(c_45005, plain, (![B_7410]: (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0(B_7410)))) | ~m1_pre_topc(B_7410, '#skF_3'('#skF_5')) | v2_struct_0(B_7410))), inference(negUnitSimplification, [status(thm)], [c_12496, c_45004])).
% 28.75/17.12  tff(c_58875, plain, (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58614, c_45005])).
% 28.75/17.12  tff(c_59480, plain, (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12605, c_58875])).
% 28.75/17.12  tff(c_59481, plain, (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_12496, c_59480])).
% 28.75/17.12  tff(c_61608, plain, (k6_domain_1(u1_struct_0('#skF_3'('#skF_5')), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_3'('#skF_5'))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_59471, c_36])).
% 28.75/17.12  tff(c_61661, plain, (u1_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))=k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_2, c_58614, c_59481, c_58614, c_61608])).
% 28.75/17.12  tff(c_61662, plain, (u1_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))=k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_12496, c_59742, c_61661])).
% 28.75/17.12  tff(c_68576, plain, (u1_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))=k1_tarski('#skF_1'(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_65724, c_61662])).
% 28.75/17.12  tff(c_64093, plain, (![B_11085]: (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(negUnitSimplification, [status(thm)], [c_70, c_64092])).
% 28.75/17.12  tff(c_68598, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | ~m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_68576, c_64093])).
% 28.75/17.12  tff(c_69077, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_59471, c_68598])).
% 28.75/17.12  tff(c_69078, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))), inference(negUnitSimplification, [status(thm)], [c_59742, c_69077])).
% 28.75/17.12  tff(c_65418, plain, (![B_11526]: (l1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11526)))) | ~l1_pre_topc('#skF_5') | ~m1_pre_topc(B_11526, '#skF_3'('#skF_5')) | v2_struct_0(B_11526))), inference(resolution, [status(thm)], [c_65372, c_8])).
% 28.75/17.12  tff(c_65507, plain, (![B_11526]: (l1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11526)))) | ~m1_pre_topc(B_11526, '#skF_3'('#skF_5')) | v2_struct_0(B_11526))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_65418])).
% 28.75/17.12  tff(c_68589, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | ~m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_68576, c_65507])).
% 28.75/17.12  tff(c_69068, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_59471, c_68589])).
% 28.75/17.12  tff(c_69069, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))), inference(negUnitSimplification, [status(thm)], [c_59742, c_69068])).
% 28.75/17.12  tff(c_64089, plain, (![B_11085]: (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(negUnitSimplification, [status(thm)], [c_70, c_64088])).
% 28.75/17.12  tff(c_68595, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | ~m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_68576, c_64089])).
% 28.75/17.12  tff(c_69074, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_59471, c_68595])).
% 28.75/17.12  tff(c_69075, plain, (v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))), inference(negUnitSimplification, [status(thm)], [c_59742, c_69074])).
% 28.75/17.12  tff(c_59303, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58614, c_4])).
% 28.75/17.12  tff(c_59749, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_59303])).
% 28.75/17.12  tff(c_6625, plain, (![B_2264, A_2265]: (v2_struct_0(B_2264) | ~v7_struct_0(A_2265) | g1_pre_topc(u1_struct_0(B_2264), u1_pre_topc(B_2264))=g1_pre_topc(u1_struct_0(A_2265), u1_pre_topc(A_2265)) | ~m1_pre_topc(B_2264, A_2265) | ~l1_pre_topc(A_2265) | v2_struct_0(A_2265))), inference(resolution, [status(thm)], [c_289, c_30])).
% 28.75/17.12  tff(c_6686, plain, (![A_41]: (v2_struct_0('#skF_3'(A_41)) | ~v7_struct_0(A_41) | g1_pre_topc(u1_struct_0('#skF_3'(A_41)), u1_pre_topc('#skF_3'(A_41)))=g1_pre_topc(u1_struct_0(A_41), u1_pre_topc(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_56, c_6625])).
% 28.75/17.12  tff(c_59055, plain, (v2_struct_0('#skF_3'('#skF_5')) | ~v7_struct_0('#skF_5') | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_3'('#skF_5')))=g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_58614, c_6686])).
% 28.75/17.12  tff(c_59587, plain, (v2_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_3'('#skF_5')))=g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_68, c_59055])).
% 28.75/17.12  tff(c_59588, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_3'('#skF_5')))=g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_12496, c_59587])).
% 28.75/17.12  tff(c_60438, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_59749, c_59588])).
% 28.75/17.12  tff(c_64081, plain, (![B_11085]: (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085))), '#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(negUnitSimplification, [status(thm)], [c_70, c_64080])).
% 28.75/17.12  tff(c_68592, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))), '#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_68576, c_64081])).
% 28.75/17.12  tff(c_69071, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))), '#skF_5') | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_59471, c_68592])).
% 28.75/17.12  tff(c_69072, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_59742, c_69071])).
% 28.75/17.12  tff(c_5806, plain, (![A_1126, A_1125]: (v2_struct_0(A_1126) | ~v7_struct_0(A_1125) | g1_pre_topc(u1_struct_0(A_1125), u1_pre_topc(A_1125))=A_1126 | ~m1_pre_topc(A_1126, A_1125) | ~l1_pre_topc(A_1125) | v2_struct_0(A_1125) | ~v1_pre_topc(A_1126) | ~l1_pre_topc(A_1126))), inference(resolution, [status(thm)], [c_3102, c_30])).
% 28.75/17.12  tff(c_69745, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | ~v7_struct_0('#skF_5') | k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))=g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))), inference(resolution, [status(thm)], [c_69072, c_5806])).
% 28.75/17.12  tff(c_69828, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))='#skF_3'('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69069, c_69075, c_84, c_60438, c_68, c_69745])).
% 28.75/17.12  tff(c_69829, plain, (k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_69078, c_69828])).
% 28.75/17.12  tff(c_46, plain, (![A_39, B_40]: (v7_struct_0(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_178])).
% 28.75/17.12  tff(c_64046, plain, (![B_11085]: (v7_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(resolution, [status(thm)], [c_64036, c_46])).
% 28.75/17.12  tff(c_64084, plain, (![B_11085]: (v7_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64046])).
% 28.75/17.12  tff(c_64085, plain, (![B_11085]: (v7_struct_0(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0(B_11085)))) | ~m1_pre_topc(B_11085, '#skF_3'('#skF_5')) | v2_struct_0(B_11085))), inference(negUnitSimplification, [status(thm)], [c_70, c_64084])).
% 28.75/17.12  tff(c_68601, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | ~m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_68576, c_64085])).
% 28.75/17.12  tff(c_69080, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5')))))) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_59471, c_68601])).
% 28.75/17.12  tff(c_69081, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_1'(u1_struct_0('#skF_5'))))))), inference(negUnitSimplification, [status(thm)], [c_59742, c_69080])).
% 28.75/17.12  tff(c_70104, plain, (v7_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_69829, c_69081])).
% 28.75/17.12  tff(c_70109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12698, c_70104])).
% 28.75/17.12  tff(c_70110, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_58612])).
% 28.75/17.12  tff(c_70114, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70110, c_10])).
% 28.75/17.12  tff(c_70117, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58613, c_70114])).
% 28.75/17.12  tff(c_70119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_70117])).
% 28.75/17.12  tff(c_70121, plain, (v7_struct_0('#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_12584])).
% 28.75/17.12  tff(c_70120, plain, (g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_12584])).
% 28.75/17.12  tff(c_70340, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_3'('#skF_5') | ~m1_pre_topc(B_45, '#skF_3'('#skF_5')) | v1_tex_2(B_45, '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_70120])).
% 28.75/17.12  tff(c_70449, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_3'('#skF_5') | ~m1_pre_topc(B_45, '#skF_3'('#skF_5')) | v1_tex_2(B_45, '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_70340])).
% 28.75/17.12  tff(c_71367, plain, (![B_12872]: (g1_pre_topc(u1_struct_0(B_12872), u1_pre_topc(B_12872))='#skF_3'('#skF_5') | ~m1_pre_topc(B_12872, '#skF_3'('#skF_5')) | v1_tex_2(B_12872, '#skF_3'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_12496, c_70449])).
% 28.75/17.12  tff(c_72899, plain, (![A_13074, B_13075]: (m1_pre_topc('#skF_3'('#skF_5'), A_13074) | ~m1_pre_topc(B_13075, A_13074) | ~l1_pre_topc(A_13074) | ~m1_pre_topc(B_13075, '#skF_3'('#skF_5')) | v1_tex_2(B_13075, '#skF_3'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_71367, c_24])).
% 28.75/17.12  tff(c_76919, plain, (![A_13639]: (m1_pre_topc('#skF_3'('#skF_5'), A_13639) | ~m1_pre_topc('#skF_3'(A_13639), '#skF_3'('#skF_5')) | v1_tex_2('#skF_3'(A_13639), '#skF_3'('#skF_5')) | ~l1_pre_topc(A_13639) | v2_struct_0(A_13639))), inference(resolution, [status(thm)], [c_56, c_72899])).
% 28.75/17.12  tff(c_12542, plain, (~v1_tex_2('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12502, c_50])).
% 28.75/17.12  tff(c_12598, plain, (~v1_tex_2('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_12542])).
% 28.75/17.12  tff(c_12599, plain, (~v1_tex_2('#skF_3'('#skF_5'), '#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_12496, c_12598])).
% 28.75/17.12  tff(c_76922, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_5') | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76919, c_12599])).
% 28.75/17.12  tff(c_76954, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_12605, c_76922])).
% 28.75/17.12  tff(c_76955, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_76954])).
% 28.75/17.12  tff(c_396, plain, (![B_122, A_123]: (v2_struct_0(B_122) | ~v7_struct_0(A_123) | g1_pre_topc(u1_struct_0(B_122), u1_pre_topc(B_122))=g1_pre_topc(u1_struct_0(A_123), u1_pre_topc(A_123)) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_289, c_30])).
% 28.75/17.12  tff(c_76984, plain, (v2_struct_0('#skF_3'('#skF_5')) | ~v7_struct_0('#skF_5') | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))=g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76955, c_396])).
% 28.75/17.12  tff(c_77020, plain, (v2_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_3'('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_70120, c_68, c_76984])).
% 28.75/17.12  tff(c_77021, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_12496, c_77020])).
% 28.75/17.12  tff(c_77139, plain, (![A_3]: (A_3='#skF_3'('#skF_5') | ~m1_pre_topc(A_3, '#skF_5') | v1_tex_2(A_3, '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_77021, c_383])).
% 28.75/17.12  tff(c_77360, plain, (![A_3]: (A_3='#skF_3'('#skF_5') | ~m1_pre_topc(A_3, '#skF_5') | v1_tex_2(A_3, '#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_77139])).
% 28.75/17.12  tff(c_77974, plain, (![A_13788]: (A_13788='#skF_3'('#skF_5') | ~m1_pre_topc(A_13788, '#skF_5') | v1_tex_2(A_13788, '#skF_5') | ~v1_pre_topc(A_13788) | ~l1_pre_topc(A_13788))), inference(negUnitSimplification, [status(thm)], [c_70, c_77360])).
% 28.75/17.12  tff(c_77981, plain, (![A_13788]: (v2_struct_0(A_13788) | ~l1_pre_topc('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5') | A_13788='#skF_3'('#skF_5') | ~m1_pre_topc(A_13788, '#skF_5') | ~v1_pre_topc(A_13788) | ~l1_pre_topc(A_13788))), inference(resolution, [status(thm)], [c_77974, c_30])).
% 28.75/17.12  tff(c_77992, plain, (![A_13788]: (v2_struct_0(A_13788) | v2_struct_0('#skF_5') | A_13788='#skF_3'('#skF_5') | ~m1_pre_topc(A_13788, '#skF_5') | ~v1_pre_topc(A_13788) | ~l1_pre_topc(A_13788))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_84, c_77981])).
% 28.75/17.12  tff(c_77999, plain, (![A_13813]: (v2_struct_0(A_13813) | A_13813='#skF_3'('#skF_5') | ~m1_pre_topc(A_13813, '#skF_5') | ~v1_pre_topc(A_13813) | ~l1_pre_topc(A_13813))), inference(negUnitSimplification, [status(thm)], [c_70, c_77992])).
% 28.75/17.12  tff(c_78022, plain, (v2_struct_0('#skF_2'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_77999])).
% 28.75/17.12  tff(c_78050, plain, (v2_struct_0('#skF_2'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7765, c_7776, c_78022])).
% 28.75/17.12  tff(c_78051, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_10604, c_78050])).
% 28.75/17.12  tff(c_10607, plain, ('#skF_3'('#skF_2'('#skF_5'))='#skF_2'('#skF_5') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5'))), inference(resolution, [status(thm)], [c_6624, c_10604])).
% 28.75/17.12  tff(c_10610, plain, ('#skF_3'('#skF_2'('#skF_5'))='#skF_2'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_7776, c_10607])).
% 28.75/17.12  tff(c_10656, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10610, c_56])).
% 28.75/17.12  tff(c_10712, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_10656])).
% 28.75/17.12  tff(c_10713, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_2'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_10604, c_10712])).
% 28.75/17.12  tff(c_72907, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | ~m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5')) | v1_tex_2('#skF_2'('#skF_5'), '#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_10713, c_72899])).
% 28.75/17.12  tff(c_72944, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5')) | ~m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5')) | v1_tex_2('#skF_2'('#skF_5'), '#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_72907])).
% 28.75/17.12  tff(c_72968, plain, (~m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_72944])).
% 28.75/17.12  tff(c_78067, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78051, c_72968])).
% 28.75/17.12  tff(c_78089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12605, c_78067])).
% 28.75/17.12  tff(c_78091, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_72944])).
% 28.75/17.12  tff(c_70167, plain, (![A_3]: (A_3='#skF_3'('#skF_5') | ~m1_pre_topc(A_3, '#skF_3'('#skF_5')) | v1_tex_2(A_3, '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_70120, c_383])).
% 28.75/17.12  tff(c_70369, plain, (![A_3]: (A_3='#skF_3'('#skF_5') | ~m1_pre_topc(A_3, '#skF_3'('#skF_5')) | v1_tex_2(A_3, '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_70167])).
% 28.75/17.12  tff(c_71991, plain, (![A_12923]: (A_12923='#skF_3'('#skF_5') | ~m1_pre_topc(A_12923, '#skF_3'('#skF_5')) | v1_tex_2(A_12923, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_12923) | ~l1_pre_topc(A_12923))), inference(negUnitSimplification, [status(thm)], [c_12496, c_70369])).
% 28.75/17.12  tff(c_72005, plain, (![A_12923]: (v2_struct_0(A_12923) | ~l1_pre_topc('#skF_3'('#skF_5')) | ~v7_struct_0('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | A_12923='#skF_3'('#skF_5') | ~m1_pre_topc(A_12923, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_12923) | ~l1_pre_topc(A_12923))), inference(resolution, [status(thm)], [c_71991, c_30])).
% 28.75/17.12  tff(c_72025, plain, (![A_12923]: (v2_struct_0(A_12923) | v2_struct_0('#skF_3'('#skF_5')) | A_12923='#skF_3'('#skF_5') | ~m1_pre_topc(A_12923, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_12923) | ~l1_pre_topc(A_12923))), inference(demodulation, [status(thm), theory('equality')], [c_70121, c_8063, c_72005])).
% 28.75/17.12  tff(c_72026, plain, (![A_12923]: (v2_struct_0(A_12923) | A_12923='#skF_3'('#skF_5') | ~m1_pre_topc(A_12923, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_12923) | ~l1_pre_topc(A_12923))), inference(negUnitSimplification, [status(thm)], [c_12496, c_72025])).
% 28.75/17.12  tff(c_78096, plain, (v2_struct_0('#skF_2'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5'))), inference(resolution, [status(thm)], [c_78091, c_72026])).
% 28.75/17.12  tff(c_78126, plain, (v2_struct_0('#skF_2'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_7776, c_78096])).
% 28.75/17.12  tff(c_78127, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_10604, c_78126])).
% 28.75/17.12  tff(c_10635, plain, (v2_struct_0('#skF_3'('#skF_2'('#skF_5'))) | ~v7_struct_0('#skF_2'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_2'('#skF_5'))), u1_pre_topc('#skF_2'('#skF_5')))='#skF_2'('#skF_5') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10610, c_2965])).
% 28.75/17.12  tff(c_10691, plain, (~v7_struct_0('#skF_2'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')), u1_pre_topc('#skF_2'('#skF_5')))='#skF_2'('#skF_5') | v2_struct_0('#skF_2'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_7776, c_10610, c_10610, c_10635])).
% 28.75/17.12  tff(c_10692, plain, (~v7_struct_0('#skF_2'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')), u1_pre_topc('#skF_2'('#skF_5')))='#skF_2'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_10604, c_10691])).
% 28.75/17.12  tff(c_12093, plain, (~v7_struct_0('#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_10692])).
% 28.75/17.12  tff(c_78169, plain, (~v7_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78127, c_12093])).
% 28.75/17.12  tff(c_78182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70121, c_78169])).
% 28.75/17.12  tff(c_78183, plain, (g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')), u1_pre_topc('#skF_2'('#skF_5')))='#skF_2'('#skF_5')), inference(splitRight, [status(thm)], [c_10692])).
% 28.75/17.12  tff(c_78397, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_2'('#skF_5') | ~m1_pre_topc(B_45, '#skF_2'('#skF_5')) | v1_tex_2(B_45, '#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_78183])).
% 28.75/17.12  tff(c_78505, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_2'('#skF_5') | ~m1_pre_topc(B_45, '#skF_2'('#skF_5')) | v1_tex_2(B_45, '#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_78397])).
% 28.75/17.12  tff(c_78686, plain, (![B_13935]: (g1_pre_topc(u1_struct_0(B_13935), u1_pre_topc(B_13935))='#skF_2'('#skF_5') | ~m1_pre_topc(B_13935, '#skF_2'('#skF_5')) | v1_tex_2(B_13935, '#skF_2'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_10604, c_78505])).
% 28.75/17.12  tff(c_64, plain, (![C_56]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_4', C_56)), u1_pre_topc(k1_tex_2('#skF_4', C_56)))!=g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~m1_subset_1(C_56, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_252])).
% 28.75/17.12  tff(c_78850, plain, (![C_56]: (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))!='#skF_2'('#skF_5') | ~m1_subset_1(C_56, u1_struct_0('#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_4', C_56), '#skF_2'('#skF_5')) | v1_tex_2(k1_tex_2('#skF_4', C_56), '#skF_2'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_78686, c_64])).
% 28.75/17.12  tff(c_94811, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))!='#skF_2'('#skF_5')), inference(splitLeft, [status(thm)], [c_78850])).
% 28.75/17.12  tff(c_94841, plain, (![A_3]: (A_3!='#skF_2'('#skF_5') | ~m1_pre_topc(A_3, '#skF_5') | v1_tex_2(A_3, '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_383, c_94811])).
% 28.75/17.12  tff(c_94870, plain, (![A_3]: (A_3!='#skF_2'('#skF_5') | ~m1_pre_topc(A_3, '#skF_5') | v1_tex_2(A_3, '#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_94841])).
% 28.75/17.12  tff(c_94992, plain, (![A_16672]: (A_16672!='#skF_2'('#skF_5') | ~m1_pre_topc(A_16672, '#skF_5') | v1_tex_2(A_16672, '#skF_5') | ~v1_pre_topc(A_16672) | ~l1_pre_topc(A_16672))), inference(negUnitSimplification, [status(thm)], [c_70, c_94870])).
% 28.75/17.12  tff(c_94999, plain, (![A_16672]: (v2_struct_0(A_16672) | ~l1_pre_topc('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5') | A_16672!='#skF_2'('#skF_5') | ~m1_pre_topc(A_16672, '#skF_5') | ~v1_pre_topc(A_16672) | ~l1_pre_topc(A_16672))), inference(resolution, [status(thm)], [c_94992, c_30])).
% 28.75/17.12  tff(c_95010, plain, (![A_16672]: (v2_struct_0(A_16672) | v2_struct_0('#skF_5') | A_16672!='#skF_2'('#skF_5') | ~m1_pre_topc(A_16672, '#skF_5') | ~v1_pre_topc(A_16672) | ~l1_pre_topc(A_16672))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_84, c_94999])).
% 28.75/17.12  tff(c_95028, plain, (![A_16721]: (v2_struct_0(A_16721) | A_16721!='#skF_2'('#skF_5') | ~m1_pre_topc(A_16721, '#skF_5') | ~v1_pre_topc(A_16721) | ~l1_pre_topc(A_16721))), inference(negUnitSimplification, [status(thm)], [c_70, c_95010])).
% 28.75/17.12  tff(c_95044, plain, (v2_struct_0('#skF_2'('#skF_5')) | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_95028])).
% 28.75/17.12  tff(c_95062, plain, (v2_struct_0('#skF_2'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7765, c_7776, c_95044])).
% 28.75/17.12  tff(c_95064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_10604, c_95062])).
% 28.75/17.12  tff(c_95066, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_2'('#skF_5')), inference(splitRight, [status(thm)], [c_78850])).
% 28.75/17.12  tff(c_95337, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_2'('#skF_5') | ~m1_pre_topc(B_45, '#skF_5') | v1_tex_2(B_45, '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_95066])).
% 28.75/17.12  tff(c_95463, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_2'('#skF_5') | ~m1_pre_topc(B_45, '#skF_5') | v1_tex_2(B_45, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_95337])).
% 28.75/17.12  tff(c_95699, plain, (![B_16845]: (g1_pre_topc(u1_struct_0(B_16845), u1_pre_topc(B_16845))='#skF_2'('#skF_5') | ~m1_pre_topc(B_16845, '#skF_5') | v1_tex_2(B_16845, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_95463])).
% 28.75/17.12  tff(c_80592, plain, (v2_struct_0('#skF_3'('#skF_3'('#skF_5'))) | ~v7_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_3'('#skF_5'))), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_80567, c_2965])).
% 28.75/17.12  tff(c_80648, plain, (~v7_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5') | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_80567, c_80567, c_80592])).
% 28.75/17.12  tff(c_80649, plain, (~v7_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80561, c_80648])).
% 28.75/17.12  tff(c_80965, plain, (~v7_struct_0('#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_80649])).
% 28.75/17.12  tff(c_85742, plain, (![A_14974]: (v2_struct_0('#skF_3'(A_14974)) | ~v7_struct_0(A_14974) | g1_pre_topc(u1_struct_0('#skF_3'(A_14974)), u1_pre_topc('#skF_3'(A_14974)))=g1_pre_topc(u1_struct_0(A_14974), u1_pre_topc(A_14974)) | ~l1_pre_topc(A_14974) | v2_struct_0(A_14974))), inference(resolution, [status(thm)], [c_56, c_6625])).
% 28.75/17.12  tff(c_184, plain, (![B_92, A_93]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_92), u1_pre_topc(B_92))) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_173, c_8])).
% 28.75/17.12  tff(c_193, plain, (![B_23, A_21]: (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_23), u1_pre_topc(B_23))), u1_pre_topc(g1_pre_topc(u1_struct_0(B_23), u1_pre_topc(B_23))))) | ~m1_pre_topc(B_23, A_21) | ~l1_pre_topc(A_21))), inference(resolution, [status(thm)], [c_24, c_184])).
% 28.75/17.12  tff(c_8329, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8316, c_193])).
% 28.75/17.12  tff(c_8361, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8329])).
% 28.75/17.12  tff(c_84070, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))), u1_pre_topc('#skF_3'('#skF_5')))) | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8361])).
% 28.75/17.12  tff(c_84234, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))), u1_pre_topc('#skF_3'('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_84070])).
% 28.75/17.12  tff(c_85763, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))), u1_pre_topc('#skF_3'('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5')) | ~v7_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_85742, c_84234])).
% 28.75/17.12  tff(c_86129, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))), u1_pre_topc('#skF_3'('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_68, c_85763])).
% 28.75/17.12  tff(c_86130, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))), u1_pre_topc('#skF_3'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_80561, c_86129])).
% 28.75/17.12  tff(c_86354, plain, (![B_45]: (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))), u1_pre_topc('#skF_3'('#skF_5')))) | ~m1_pre_topc(B_45, '#skF_5') | v1_tex_2(B_45, '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_86130])).
% 28.75/17.12  tff(c_86418, plain, (![B_45]: (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))), u1_pre_topc('#skF_3'('#skF_5')))) | ~m1_pre_topc(B_45, '#skF_5') | v1_tex_2(B_45, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_86354])).
% 28.75/17.12  tff(c_89104, plain, (![B_15241]: (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(B_15241), u1_pre_topc(B_15241))), u1_pre_topc('#skF_3'('#skF_5')))) | ~m1_pre_topc(B_15241, '#skF_5') | v1_tex_2(B_15241, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_86418])).
% 28.75/17.12  tff(c_89119, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))) | ~m1_pre_topc('#skF_2'('#skF_5'), '#skF_5') | v1_tex_2('#skF_2'('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_78183, c_89104])).
% 28.75/17.12  tff(c_89319, plain, (~m1_pre_topc('#skF_2'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_89119])).
% 28.75/17.12  tff(c_89322, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_89319])).
% 28.75/17.12  tff(c_89325, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_89322])).
% 28.75/17.12  tff(c_89327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_89325])).
% 28.75/17.12  tff(c_89329, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_89119])).
% 28.75/17.12  tff(c_89331, plain, (v2_struct_0('#skF_2'('#skF_5')) | ~v7_struct_0('#skF_5') | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_2'('#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5'))), inference(resolution, [status(thm)], [c_89329, c_5806])).
% 28.75/17.12  tff(c_89363, plain, (v2_struct_0('#skF_2'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_2'('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_7776, c_84, c_68, c_89331])).
% 28.75/17.12  tff(c_89364, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_2'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_10604, c_89363])).
% 28.75/17.12  tff(c_89512, plain, (![A_3]: (A_3='#skF_2'('#skF_5') | ~m1_pre_topc(A_3, '#skF_5') | v1_tex_2(A_3, '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_89364, c_383])).
% 28.75/17.12  tff(c_89732, plain, (![A_3]: (A_3='#skF_2'('#skF_5') | ~m1_pre_topc(A_3, '#skF_5') | v1_tex_2(A_3, '#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_89512])).
% 28.75/17.12  tff(c_90257, plain, (![A_15435]: (A_15435='#skF_2'('#skF_5') | ~m1_pre_topc(A_15435, '#skF_5') | v1_tex_2(A_15435, '#skF_5') | ~v1_pre_topc(A_15435) | ~l1_pre_topc(A_15435))), inference(negUnitSimplification, [status(thm)], [c_70, c_89732])).
% 28.75/17.12  tff(c_90268, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_90257, c_50])).
% 28.75/17.12  tff(c_90279, plain, (v2_struct_0('#skF_5') | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_84, c_90268])).
% 28.75/17.12  tff(c_90280, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_90279])).
% 28.75/17.12  tff(c_90313, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_90280])).
% 28.75/17.12  tff(c_90316, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_90313])).
% 28.75/17.12  tff(c_90319, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_90316])).
% 28.75/17.12  tff(c_90321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_90319])).
% 28.75/17.12  tff(c_90322, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_90280])).
% 28.75/17.12  tff(c_81567, plain, (![A_14358, B_14359]: (m1_pre_topc('#skF_2'('#skF_5'), A_14358) | ~m1_pre_topc(B_14359, A_14358) | ~l1_pre_topc(A_14358) | ~m1_pre_topc(B_14359, '#skF_2'('#skF_5')) | v1_tex_2(B_14359, '#skF_2'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_78686, c_24])).
% 28.75/17.12  tff(c_81571, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5')) | v1_tex_2('#skF_3'('#skF_5'), '#skF_2'('#skF_5'))), inference(resolution, [status(thm)], [c_80670, c_81567])).
% 28.75/17.12  tff(c_81605, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5')) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5')) | v1_tex_2('#skF_3'('#skF_5'), '#skF_2'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_81571])).
% 28.75/17.12  tff(c_81636, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_81605])).
% 28.75/17.12  tff(c_90339, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90322, c_81636])).
% 28.75/17.12  tff(c_90362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80670, c_90339])).
% 28.75/17.12  tff(c_90364, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5'))), inference(splitRight, [status(thm)], [c_81605])).
% 28.75/17.12  tff(c_78184, plain, (v7_struct_0('#skF_2'('#skF_5'))), inference(splitRight, [status(thm)], [c_10692])).
% 28.75/17.12  tff(c_78221, plain, (![A_3]: (A_3='#skF_2'('#skF_5') | ~m1_pre_topc(A_3, '#skF_2'('#skF_5')) | v1_tex_2(A_3, '#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5')) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_78183, c_383])).
% 28.75/17.12  tff(c_78422, plain, (![A_3]: (A_3='#skF_2'('#skF_5') | ~m1_pre_topc(A_3, '#skF_2'('#skF_5')) | v1_tex_2(A_3, '#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5')) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_78221])).
% 28.75/17.12  tff(c_79055, plain, (![A_13960]: (A_13960='#skF_2'('#skF_5') | ~m1_pre_topc(A_13960, '#skF_2'('#skF_5')) | v1_tex_2(A_13960, '#skF_2'('#skF_5')) | ~v1_pre_topc(A_13960) | ~l1_pre_topc(A_13960))), inference(negUnitSimplification, [status(thm)], [c_10604, c_78422])).
% 28.75/17.12  tff(c_79069, plain, (![A_13960]: (v2_struct_0(A_13960) | ~l1_pre_topc('#skF_2'('#skF_5')) | ~v7_struct_0('#skF_2'('#skF_5')) | v2_struct_0('#skF_2'('#skF_5')) | A_13960='#skF_2'('#skF_5') | ~m1_pre_topc(A_13960, '#skF_2'('#skF_5')) | ~v1_pre_topc(A_13960) | ~l1_pre_topc(A_13960))), inference(resolution, [status(thm)], [c_79055, c_30])).
% 28.75/17.12  tff(c_79089, plain, (![A_13960]: (v2_struct_0(A_13960) | v2_struct_0('#skF_2'('#skF_5')) | A_13960='#skF_2'('#skF_5') | ~m1_pre_topc(A_13960, '#skF_2'('#skF_5')) | ~v1_pre_topc(A_13960) | ~l1_pre_topc(A_13960))), inference(demodulation, [status(thm), theory('equality')], [c_78184, c_7765, c_79069])).
% 28.75/17.12  tff(c_79090, plain, (![A_13960]: (v2_struct_0(A_13960) | A_13960='#skF_2'('#skF_5') | ~m1_pre_topc(A_13960, '#skF_2'('#skF_5')) | ~v1_pre_topc(A_13960) | ~l1_pre_topc(A_13960))), inference(negUnitSimplification, [status(thm)], [c_10604, c_79089])).
% 28.75/17.12  tff(c_90369, plain, (v2_struct_0('#skF_3'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_90364, c_79090])).
% 28.75/17.12  tff(c_90399, plain, (v2_struct_0('#skF_3'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_90369])).
% 28.75/17.12  tff(c_90400, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80561, c_90399])).
% 28.75/17.12  tff(c_90447, plain, (v7_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90400, c_78184])).
% 28.75/17.12  tff(c_90457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80965, c_90447])).
% 28.75/17.12  tff(c_90458, plain, (g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5')), inference(splitRight, [status(thm)], [c_80649])).
% 28.75/17.12  tff(c_95744, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_5') | v1_tex_2('#skF_3'('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_95699, c_90458])).
% 28.75/17.12  tff(c_96071, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_95744])).
% 28.75/17.12  tff(c_96074, plain, (~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_96071])).
% 28.75/17.12  tff(c_96077, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_96074])).
% 28.75/17.12  tff(c_96079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_96077])).
% 28.75/17.12  tff(c_96081, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_95744])).
% 28.75/17.12  tff(c_96083, plain, (v2_struct_0('#skF_3'('#skF_5')) | ~v7_struct_0('#skF_5') | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_3'('#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_96081, c_5806])).
% 28.75/17.12  tff(c_96117, plain, (v2_struct_0('#skF_3'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_84, c_95066, c_68, c_96083])).
% 28.75/17.12  tff(c_96118, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_80561, c_96117])).
% 28.75/17.12  tff(c_90549, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_3'('#skF_5') | ~m1_pre_topc(B_45, '#skF_3'('#skF_5')) | v1_tex_2(B_45, '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_90458, c_58])).
% 28.75/17.12  tff(c_90752, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_3'('#skF_5') | ~m1_pre_topc(B_45, '#skF_3'('#skF_5')) | v1_tex_2(B_45, '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_90549])).
% 28.75/17.12  tff(c_91116, plain, (![B_15679]: (g1_pre_topc(u1_struct_0(B_15679), u1_pre_topc(B_15679))='#skF_3'('#skF_5') | ~m1_pre_topc(B_15679, '#skF_3'('#skF_5')) | v1_tex_2(B_15679, '#skF_3'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_80561, c_90752])).
% 28.75/17.12  tff(c_91152, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5')) | v1_tex_2('#skF_2'('#skF_5'), '#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_91116, c_78183])).
% 28.75/17.12  tff(c_91521, plain, (~m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_91152])).
% 28.75/17.12  tff(c_96179, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96118, c_91521])).
% 28.75/17.12  tff(c_96199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80670, c_96179])).
% 28.75/17.12  tff(c_96201, plain, (m1_pre_topc('#skF_2'('#skF_5'), '#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_91152])).
% 28.75/17.12  tff(c_90459, plain, (v7_struct_0('#skF_3'('#skF_5'))), inference(splitRight, [status(thm)], [c_80649])).
% 28.75/17.12  tff(c_90523, plain, (![A_3]: (A_3='#skF_3'('#skF_5') | ~m1_pre_topc(A_3, '#skF_3'('#skF_5')) | v1_tex_2(A_3, '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_90458, c_383])).
% 28.75/17.12  tff(c_90741, plain, (![A_3]: (A_3='#skF_3'('#skF_5') | ~m1_pre_topc(A_3, '#skF_3'('#skF_5')) | v1_tex_2(A_3, '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_90523])).
% 28.75/17.12  tff(c_91019, plain, (![A_15629]: (A_15629='#skF_3'('#skF_5') | ~m1_pre_topc(A_15629, '#skF_3'('#skF_5')) | v1_tex_2(A_15629, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_15629) | ~l1_pre_topc(A_15629))), inference(negUnitSimplification, [status(thm)], [c_80561, c_90741])).
% 28.75/17.12  tff(c_91033, plain, (![A_15629]: (v2_struct_0(A_15629) | ~l1_pre_topc('#skF_3'('#skF_5')) | ~v7_struct_0('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | A_15629='#skF_3'('#skF_5') | ~m1_pre_topc(A_15629, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_15629) | ~l1_pre_topc(A_15629))), inference(resolution, [status(thm)], [c_91019, c_30])).
% 28.75/17.12  tff(c_91053, plain, (![A_15629]: (v2_struct_0(A_15629) | v2_struct_0('#skF_3'('#skF_5')) | A_15629='#skF_3'('#skF_5') | ~m1_pre_topc(A_15629, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_15629) | ~l1_pre_topc(A_15629))), inference(demodulation, [status(thm), theory('equality')], [c_90459, c_8063, c_91033])).
% 28.75/17.12  tff(c_91054, plain, (![A_15629]: (v2_struct_0(A_15629) | A_15629='#skF_3'('#skF_5') | ~m1_pre_topc(A_15629, '#skF_3'('#skF_5')) | ~v1_pre_topc(A_15629) | ~l1_pre_topc(A_15629))), inference(negUnitSimplification, [status(thm)], [c_80561, c_91053])).
% 28.75/17.12  tff(c_96204, plain, (v2_struct_0('#skF_2'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_5'))), inference(resolution, [status(thm)], [c_96201, c_91054])).
% 28.75/17.12  tff(c_96231, plain, (v2_struct_0('#skF_2'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7765, c_7776, c_96204])).
% 28.75/17.12  tff(c_96232, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_10604, c_96231])).
% 28.75/17.12  tff(c_78506, plain, (![B_45]: (g1_pre_topc(u1_struct_0(B_45), u1_pre_topc(B_45))='#skF_2'('#skF_5') | ~m1_pre_topc(B_45, '#skF_2'('#skF_5')) | v1_tex_2(B_45, '#skF_2'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_10604, c_78505])).
% 28.75/17.12  tff(c_90571, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5')) | v1_tex_2('#skF_3'('#skF_5'), '#skF_2'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_78506, c_90458])).
% 28.75/17.12  tff(c_91018, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_90571])).
% 28.75/17.12  tff(c_96271, plain, (~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96232, c_91018])).
% 28.75/17.12  tff(c_96290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80670, c_96271])).
% 28.75/17.12  tff(c_96292, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_2'('#skF_5'))), inference(splitRight, [status(thm)], [c_90571])).
% 28.75/17.12  tff(c_96295, plain, (v2_struct_0('#skF_3'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_96292, c_79090])).
% 28.75/17.12  tff(c_96322, plain, (v2_struct_0('#skF_3'('#skF_5')) | '#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_8243, c_96295])).
% 28.75/17.12  tff(c_96323, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80561, c_96322])).
% 28.75/17.12  tff(c_96424, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_96323, c_18])).
% 28.75/17.12  tff(c_96470, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_96424])).
% 28.75/17.12  tff(c_96471, plain, (m1_pre_topc('#skF_3'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_96470])).
% 28.75/17.12  tff(c_448, plain, (![B_132, A_9]: (u1_struct_0(B_132)=u1_struct_0(A_9) | v1_xboole_0(u1_struct_0(A_9)) | v1_xboole_0(u1_struct_0(B_132)) | ~m1_pre_topc(B_132, A_9) | ~l1_pre_topc(A_9) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_445])).
% 28.75/17.12  tff(c_96497, plain, (u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~l1_struct_0('#skF_5') | ~v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_96471, c_448])).
% 28.75/17.12  tff(c_96535, plain, (u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) | ~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_84, c_96497])).
% 28.75/17.12  tff(c_97574, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_96535])).
% 28.75/17.12  tff(c_97577, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_97574])).
% 28.75/17.12  tff(c_97581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_97577])).
% 28.75/17.12  tff(c_97583, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_96535])).
% 28.75/17.12  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 28.75/17.12  tff(c_97582, plain, (v1_xboole_0(u1_struct_0('#skF_3'('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5')) | u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_96535])).
% 28.75/17.12  tff(c_97652, plain, (u1_struct_0('#skF_3'('#skF_5'))=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_97582])).
% 28.75/17.12  tff(c_104772, plain, (![B_19481, A_19482, A_19483]: (m1_subset_1('#skF_1'(u1_struct_0(B_19481)), u1_struct_0(A_19482)) | ~m1_pre_topc(A_19483, A_19482) | ~l1_pre_topc(A_19482) | v2_struct_0(A_19482) | ~m1_pre_topc(B_19481, A_19483) | v2_struct_0(B_19481) | ~l1_pre_topc(A_19483) | v2_struct_0(A_19483))), inference(resolution, [status(thm)], [c_252, c_20])).
% 28.75/17.12  tff(c_104808, plain, (![B_19481]: (m1_subset_1('#skF_1'(u1_struct_0(B_19481)), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_19481, '#skF_5') | v2_struct_0(B_19481) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_104772])).
% 28.75/17.12  tff(c_104855, plain, (![B_19481]: (m1_subset_1('#skF_1'(u1_struct_0(B_19481)), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_19481, '#skF_5') | v2_struct_0(B_19481) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_72, c_104808])).
% 28.75/17.12  tff(c_104860, plain, (![B_19508]: (m1_subset_1('#skF_1'(u1_struct_0(B_19508)), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_19508, '#skF_5') | v2_struct_0(B_19508))), inference(negUnitSimplification, [status(thm)], [c_70, c_74, c_104855])).
% 28.75/17.12  tff(c_104882, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_5') | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_97652, c_104860])).
% 28.75/17.12  tff(c_104917, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96471, c_104882])).
% 28.75/17.12  tff(c_104918, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80561, c_104917])).
% 28.75/17.12  tff(c_104925, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_104918, c_38])).
% 28.75/17.12  tff(c_104944, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_104925])).
% 28.75/17.12  tff(c_104945, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_104944])).
% 28.75/17.12  tff(c_105022, plain, (l1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_104945, c_8])).
% 28.75/17.12  tff(c_105077, plain, (l1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_105022])).
% 28.75/17.12  tff(c_104931, plain, (v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_104918, c_44])).
% 28.75/17.12  tff(c_104952, plain, (v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_104931])).
% 28.75/17.12  tff(c_104953, plain, (v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_104952])).
% 28.75/17.12  tff(c_97811, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_97652, c_10])).
% 28.75/17.12  tff(c_97933, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80561, c_97811])).
% 28.75/17.12  tff(c_97937, plain, (~l1_struct_0('#skF_3'('#skF_5'))), inference(splitLeft, [status(thm)], [c_97933])).
% 28.75/17.12  tff(c_97940, plain, (~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_97937])).
% 28.75/17.12  tff(c_97944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8063, c_97940])).
% 28.75/17.12  tff(c_97945, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_97933])).
% 28.75/17.12  tff(c_97796, plain, (~v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_97652, c_158])).
% 28.75/17.12  tff(c_97924, plain, (~v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_97796])).
% 28.75/17.12  tff(c_97925, plain, (~v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_80561, c_97924])).
% 28.75/17.12  tff(c_228, plain, (![A_101, B_102]: (m1_pre_topc(k1_tex_2(A_101, B_102), A_101) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_164])).
% 28.75/17.12  tff(c_234, plain, (![A_105]: (m1_pre_topc(k1_tex_2(A_105, '#skF_1'(u1_struct_0(A_105))), A_105) | ~l1_pre_topc(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_2, c_228])).
% 28.75/17.12  tff(c_244, plain, (![A_105]: (l1_pre_topc(k1_tex_2(A_105, '#skF_1'(u1_struct_0(A_105)))) | ~l1_pre_topc(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_234, c_8])).
% 28.75/17.12  tff(c_97767, plain, (l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_97652, c_244])).
% 28.75/17.12  tff(c_97897, plain, (l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_97767])).
% 28.75/17.12  tff(c_97898, plain, (l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_80561, c_97897])).
% 28.75/17.12  tff(c_166, plain, (![A_87, B_88]: (v1_pre_topc(k1_tex_2(A_87, B_88)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_178])).
% 28.75/17.12  tff(c_171, plain, (![A_87]: (v1_pre_topc(k1_tex_2(A_87, '#skF_1'(u1_struct_0(A_87)))) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_2, c_166])).
% 28.75/17.12  tff(c_97790, plain, (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_97652, c_171])).
% 28.75/17.12  tff(c_97918, plain, (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_97790])).
% 28.75/17.12  tff(c_97919, plain, (v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_80561, c_97918])).
% 28.75/17.12  tff(c_97653, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_3'('#skF_5')))='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_97652, c_90458])).
% 28.75/17.12  tff(c_232, plain, (![A_101]: (m1_pre_topc(k1_tex_2(A_101, '#skF_1'(u1_struct_0(A_101))), A_101) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(resolution, [status(thm)], [c_2, c_228])).
% 28.75/17.12  tff(c_97770, plain, (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_97652, c_232])).
% 28.75/17.12  tff(c_97900, plain, (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_97770])).
% 28.75/17.12  tff(c_97901, plain, (m1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))), '#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80561, c_97900])).
% 28.75/17.12  tff(c_98300, plain, (v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~v7_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))=k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_97901, c_5806])).
% 28.75/17.12  tff(c_98338, plain, (v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))='#skF_3'('#skF_5') | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_97898, c_97919, c_8063, c_97653, c_97652, c_90459, c_98300])).
% 28.75/17.12  tff(c_98339, plain, (k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80561, c_97925, c_98338])).
% 28.75/17.12  tff(c_98411, plain, (k6_domain_1(u1_struct_0('#skF_3'('#skF_5')), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_pre_topc('#skF_3'('#skF_5'), '#skF_3'('#skF_5')) | ~v1_pre_topc(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0(k1_tex_2('#skF_3'('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_3'('#skF_5'))) | ~l1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_98339, c_36])).
% 28.75/17.12  tff(c_98445, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0('#skF_5') | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_2, c_97652, c_98339, c_8243, c_98339, c_80670, c_97652, c_98339, c_97652, c_98411])).
% 28.75/17.12  tff(c_98446, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80561, c_98445])).
% 28.75/17.12  tff(c_98478, plain, (k1_tarski('#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_98446, c_121])).
% 28.75/17.12  tff(c_98493, plain, (k1_tarski('#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_97945, c_98478])).
% 28.75/17.12  tff(c_104937, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(u1_struct_0('#skF_5')))=k1_tarski('#skF_1'(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_104918, c_22])).
% 28.75/17.12  tff(c_104959, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98493, c_104937])).
% 28.75/17.12  tff(c_105467, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_104959])).
% 28.75/17.12  tff(c_105470, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_105467, c_10])).
% 28.75/17.12  tff(c_105473, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_105470])).
% 28.75/17.12  tff(c_105476, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_105473])).
% 28.75/17.12  tff(c_105480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_105476])).
% 28.75/17.12  tff(c_105481, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_104959])).
% 28.75/17.12  tff(c_104934, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_104918, c_48])).
% 28.75/17.12  tff(c_104956, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_104934])).
% 28.75/17.12  tff(c_104957, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_104956])).
% 28.75/17.12  tff(c_105009, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | ~v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_104945, c_36])).
% 28.75/17.12  tff(c_105058, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_104918, c_104953, c_105009])).
% 28.75/17.12  tff(c_105059, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(u1_struct_0('#skF_5')))=u1_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_104957, c_105058])).
% 28.75/17.12  tff(c_106280, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))))=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105481, c_105059])).
% 28.75/17.12  tff(c_106538, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))))=k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))) | ~v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_106280, c_4])).
% 28.75/17.12  tff(c_106728, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))))=k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_105077, c_104953, c_106538])).
% 28.75/17.12  tff(c_96488, plain, (v2_struct_0('#skF_3'('#skF_5')) | ~v7_struct_0('#skF_5') | g1_pre_topc(u1_struct_0('#skF_3'('#skF_5')), u1_pre_topc('#skF_3'('#skF_5')))=g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_96471, c_396])).
% 28.75/17.12  tff(c_96520, plain, (v2_struct_0('#skF_3'('#skF_5')) | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_3'('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_90458, c_68, c_96488])).
% 28.75/17.12  tff(c_96521, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_3'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_80561, c_96520])).
% 28.75/17.12  tff(c_96560, plain, (![C_56]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_4', C_56)), u1_pre_topc(k1_tex_2('#skF_4', C_56)))!='#skF_3'('#skF_5') | ~m1_subset_1(C_56, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_96521, c_64])).
% 28.75/17.12  tff(c_106391, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))))!='#skF_3'('#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_106280, c_96560])).
% 28.75/17.12  tff(c_106633, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))))!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104918, c_106391])).
% 28.75/17.12  tff(c_107687, plain, (k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106728, c_106633])).
% 28.75/17.12  tff(c_96627, plain, (![A_21]: (m1_pre_topc('#skF_3'('#skF_5'), A_21) | ~m1_pre_topc('#skF_5', A_21) | ~l1_pre_topc(A_21))), inference(superposition, [status(thm), theory('equality')], [c_96521, c_24])).
% 28.75/17.12  tff(c_34, plain, (![A_30, B_34, C_36]: (k1_tex_2(A_30, B_34)=C_36 | u1_struct_0(C_36)!=k6_domain_1(u1_struct_0(A_30), B_34) | ~m1_pre_topc(C_36, A_30) | ~v1_pre_topc(C_36) | v2_struct_0(C_36) | ~m1_subset_1(B_34, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_150])).
% 28.75/17.12  tff(c_105786, plain, (![C_36]: (k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))=C_36 | u1_struct_0(C_36)!=u1_struct_0('#skF_5') | ~m1_pre_topc(C_36, '#skF_4') | ~v1_pre_topc(C_36) | v2_struct_0(C_36) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_105481, c_34])).
% 28.75/17.12  tff(c_105802, plain, (![C_36]: (k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))=C_36 | u1_struct_0(C_36)!=u1_struct_0('#skF_5') | ~m1_pre_topc(C_36, '#skF_4') | ~v1_pre_topc(C_36) | v2_struct_0(C_36) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_104918, c_105786])).
% 28.75/17.12  tff(c_110546, plain, (![C_21407]: (k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))=C_21407 | u1_struct_0(C_21407)!=u1_struct_0('#skF_5') | ~m1_pre_topc(C_21407, '#skF_4') | ~v1_pre_topc(C_21407) | v2_struct_0(C_21407))), inference(negUnitSimplification, [status(thm)], [c_74, c_105802])).
% 28.75/17.12  tff(c_110570, plain, (k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))='#skF_3'('#skF_5') | u1_struct_0('#skF_3'('#skF_5'))!=u1_struct_0('#skF_5') | ~v1_pre_topc('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96627, c_110546])).
% 28.75/17.12  tff(c_110626, plain, (k1_tex_2('#skF_4', '#skF_1'(u1_struct_0('#skF_5')))='#skF_3'('#skF_5') | v2_struct_0('#skF_3'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_8243, c_97652, c_110570])).
% 28.75/17.12  tff(c_110628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80561, c_107687, c_110626])).
% 28.75/17.12  tff(c_110629, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))), inference(splitRight, [status(thm)], [c_97582])).
% 28.75/17.12  tff(c_110631, plain, (v1_xboole_0(u1_struct_0('#skF_3'('#skF_5')))), inference(splitLeft, [status(thm)], [c_110629])).
% 28.75/17.12  tff(c_110634, plain, (~l1_struct_0('#skF_3'('#skF_5')) | v2_struct_0('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_110631, c_10])).
% 28.75/17.12  tff(c_110637, plain, (~l1_struct_0('#skF_3'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80561, c_110634])).
% 28.75/17.12  tff(c_110640, plain, (~l1_pre_topc('#skF_3'('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_110637])).
% 28.75/17.12  tff(c_110644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8063, c_110640])).
% 28.75/17.12  tff(c_110645, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_110629])).
% 28.75/17.12  tff(c_110649, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_110645, c_10])).
% 28.75/17.12  tff(c_110652, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_97583, c_110649])).
% 28.75/17.12  tff(c_110654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110652])).
% 28.75/17.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.75/17.12  
% 28.75/17.12  Inference rules
% 28.75/17.12  ----------------------
% 28.75/17.12  #Ref     : 7
% 28.75/17.12  #Sup     : 21637
% 28.75/17.12  #Fact    : 24
% 28.75/17.12  #Define  : 0
% 28.75/17.12  #Split   : 64
% 28.75/17.12  #Chain   : 0
% 28.75/17.12  #Close   : 0
% 28.75/17.12  
% 28.75/17.12  Ordering : KBO
% 28.75/17.12  
% 28.75/17.12  Simplification rules
% 28.75/17.12  ----------------------
% 28.75/17.12  #Subsume      : 3950
% 28.75/17.12  #Demod        : 18612
% 28.75/17.12  #Tautology    : 4295
% 28.75/17.12  #SimpNegUnit  : 5924
% 28.75/17.12  #BackRed      : 588
% 28.75/17.12  
% 28.75/17.12  #Partial instantiations: 19008
% 28.75/17.12  #Strategies tried      : 1
% 28.75/17.12  
% 28.75/17.12  Timing (in seconds)
% 28.75/17.12  ----------------------
% 28.75/17.12  Preprocessing        : 0.38
% 28.75/17.12  Parsing              : 0.21
% 28.75/17.12  CNF conversion       : 0.03
% 28.75/17.12  Main loop            : 15.79
% 28.75/17.12  Inferencing          : 2.88
% 28.75/17.12  Reduction            : 5.06
% 28.75/17.12  Demodulation         : 3.82
% 28.75/17.12  BG Simplification    : 0.38
% 28.75/17.12  Subsumption          : 6.45
% 28.75/17.13  Abstraction          : 0.51
% 28.75/17.13  MUC search           : 0.00
% 28.75/17.13  Cooper               : 0.00
% 28.75/17.13  Total                : 16.34
% 28.75/17.13  Index Insertion      : 0.00
% 28.75/17.13  Index Deletion       : 0.00
% 28.75/17.13  Index Matching       : 0.00
% 28.75/17.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
