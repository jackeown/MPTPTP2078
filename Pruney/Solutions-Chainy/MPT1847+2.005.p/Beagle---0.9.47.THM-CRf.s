%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:52 EST 2020

% Result     : Theorem 9.43s
% Output     : CNFRefutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :  162 (1766 expanded)
%              Number of leaves         :   38 ( 622 expanded)
%              Depth                    :   17
%              Number of atoms          :  286 (4516 expanded)
%              Number of equality atoms :   44 ( 815 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_119,axiom,(
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

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(c_50,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_95,plain,(
    ! [B_55,A_56] :
      ( l1_pre_topc(B_55)
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_104,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_98])).

tff(c_24,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    ! [A_16] :
      ( u1_struct_0(A_16) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_118,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_85])).

tff(c_553,plain,(
    ! [B_86,A_87] :
      ( u1_struct_0(B_86) = '#skF_1'(A_87,B_86)
      | v1_tex_2(B_86,A_87)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_556,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_553,c_50])).

tff(c_559,plain,(
    k2_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_118,c_556])).

tff(c_570,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_118])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_332,plain,(
    ! [A_74,B_75] :
      ( m1_pre_topc(k1_pre_topc(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_352,plain,(
    ! [A_76] :
      ( m1_pre_topc(k1_pre_topc(A_76,u1_struct_0(A_76)),A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_62,c_332])).

tff(c_26,plain,(
    ! [B_19,A_17] :
      ( l1_pre_topc(B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_365,plain,(
    ! [A_76] :
      ( l1_pre_topc(k1_pre_topc(A_76,u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_352,c_26])).

tff(c_596,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_365])).

tff(c_635,plain,(
    l1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_596])).

tff(c_351,plain,(
    ! [A_74] :
      ( m1_pre_topc(k1_pre_topc(A_74,u1_struct_0(A_74)),A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_62,c_332])).

tff(c_599,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_351])).

tff(c_637,plain,(
    m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_599])).

tff(c_687,plain,(
    ! [A_89,B_90] :
      ( m1_pre_topc(A_89,g1_pre_topc(u1_struct_0(B_90),u1_pre_topc(B_90)))
      | ~ m1_pre_topc(A_89,B_90)
      | ~ l1_pre_topc(B_90)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_696,plain,(
    ! [A_89] :
      ( m1_pre_topc(A_89,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_89,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_687])).

tff(c_13953,plain,(
    ! [A_413] :
      ( m1_pre_topc(A_413,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_413,'#skF_4')
      | ~ l1_pre_topc(A_413) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_696])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_95])).

tff(c_107,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_101])).

tff(c_122,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_85])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_123,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_54])).

tff(c_132,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_123])).

tff(c_426,plain,(
    ! [B_78,A_79] :
      ( m1_pre_topc(B_78,A_79)
      | ~ m1_pre_topc(B_78,g1_pre_topc(u1_struct_0(A_79),u1_pre_topc(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_433,plain,(
    ! [B_78] :
      ( m1_pre_topc(B_78,'#skF_3')
      | ~ m1_pre_topc(B_78,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_426])).

tff(c_442,plain,(
    ! [B_78] :
      ( m1_pre_topc(B_78,'#skF_3')
      | ~ m1_pre_topc(B_78,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_132,c_433])).

tff(c_6869,plain,(
    ! [B_78] :
      ( m1_pre_topc(B_78,'#skF_3')
      | ~ m1_pre_topc(B_78,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_442])).

tff(c_13988,plain,(
    ! [A_414] :
      ( m1_pre_topc(A_414,'#skF_3')
      | ~ m1_pre_topc(A_414,'#skF_4')
      | ~ l1_pre_topc(A_414) ) ),
    inference(resolution,[status(thm)],[c_13953,c_6869])).

tff(c_86,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_86])).

tff(c_263,plain,(
    ! [B_69,A_70] :
      ( m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_287,plain,(
    ! [B_69] :
      ( m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_69,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_263])).

tff(c_507,plain,(
    ! [B_84] :
      ( m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_84,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_287])).

tff(c_516,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_507])).

tff(c_524,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_516])).

tff(c_46,plain,(
    ! [B_43,A_42] :
      ( v1_subset_1(B_43,A_42)
      | B_43 = A_42
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_533,plain,
    ( v1_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_524,c_46])).

tff(c_6448,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_559,c_533])).

tff(c_6449,plain,(
    k2_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6448])).

tff(c_12,plain,(
    ! [A_5] : ~ v1_subset_1(k2_subset_1(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_5] : ~ v1_subset_1(A_5,A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_52,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_513,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_507])).

tff(c_522,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_513])).

tff(c_529,plain,
    ( v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_522,c_46])).

tff(c_859,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_1063,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_559,c_859,c_559,c_533])).

tff(c_1064,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1063])).

tff(c_145,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(u1_struct_0(B_61),u1_struct_0(A_62))
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_165,plain,(
    ! [B_61] :
      ( r1_tarski(u1_struct_0(B_61),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_61,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_145])).

tff(c_239,plain,(
    ! [B_68] :
      ( r1_tarski(u1_struct_0(B_68),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_68,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_165])).

tff(c_247,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_239])).

tff(c_255,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_247])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_255,c_2])).

tff(c_1061,plain,
    ( k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),'#skF_1'('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_559,c_859,c_559,c_262])).

tff(c_1062,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),'#skF_1'('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1061])).

tff(c_1086,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_1062])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1086])).

tff(c_1106,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1063])).

tff(c_758,plain,(
    ! [A_92,B_93] :
      ( ~ v1_subset_1('#skF_1'(A_92,B_93),u1_struct_0(A_92))
      | v1_tex_2(B_93,A_92)
      | ~ m1_pre_topc(B_93,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_767,plain,(
    ! [B_93] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_93),k2_struct_0('#skF_2'))
      | v1_tex_2(B_93,'#skF_2')
      | ~ m1_pre_topc(B_93,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_758])).

tff(c_773,plain,(
    ! [B_93] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_93),k2_struct_0('#skF_2'))
      | v1_tex_2(B_93,'#skF_2')
      | ~ m1_pre_topc(B_93,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_767])).

tff(c_2797,plain,(
    ! [B_164] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_164),k2_struct_0('#skF_3'))
      | v1_tex_2(B_164,'#skF_2')
      | ~ m1_pre_topc(B_164,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_773])).

tff(c_2800,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1106,c_2797])).

tff(c_2803,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2800])).

tff(c_2805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2803])).

tff(c_2806,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1061])).

tff(c_2823,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2806,c_122])).

tff(c_901,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_90])).

tff(c_2812,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2806,c_901])).

tff(c_34,plain,(
    ! [B_28,A_26] :
      ( m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3036,plain,(
    ! [B_165,A_166] :
      ( v1_subset_1(u1_struct_0(B_165),u1_struct_0(A_166))
      | ~ m1_subset_1(u1_struct_0(B_165),k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v1_tex_2(B_165,A_166)
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3539,plain,(
    ! [B_195,A_196] :
      ( v1_subset_1(u1_struct_0(B_195),u1_struct_0(A_196))
      | ~ v1_tex_2(B_195,A_196)
      | ~ m1_pre_topc(B_195,A_196)
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_34,c_3036])).

tff(c_3555,plain,(
    ! [B_195] :
      ( v1_subset_1(u1_struct_0(B_195),'#skF_1'('#skF_2','#skF_4'))
      | ~ v1_tex_2(B_195,'#skF_2')
      | ~ m1_pre_topc(B_195,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2812,c_3539])).

tff(c_6385,plain,(
    ! [B_267] :
      ( v1_subset_1(u1_struct_0(B_267),'#skF_1'('#skF_2','#skF_4'))
      | ~ v1_tex_2(B_267,'#skF_2')
      | ~ m1_pre_topc(B_267,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3555])).

tff(c_6400,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2823,c_6385])).

tff(c_6413,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_6400])).

tff(c_6415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_6413])).

tff(c_6417,plain,(
    k2_struct_0('#skF_2') != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_244,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_239])).

tff(c_253,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_244])).

tff(c_259,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_6447,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_6417,c_259])).

tff(c_6450,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6449,c_6447])).

tff(c_201,plain,(
    ! [A_65,B_66] :
      ( v1_pre_topc(k1_pre_topc(A_65,B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_222,plain,(
    ! [A_67] :
      ( v1_pre_topc(k1_pre_topc(A_67,u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_62,c_201])).

tff(c_228,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_4',k2_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_222])).

tff(c_235,plain,(
    v1_pre_topc(k1_pre_topc('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_228])).

tff(c_568,plain,(
    v1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_235])).

tff(c_6754,plain,(
    ! [A_285,B_286] :
      ( k2_struct_0(k1_pre_topc(A_285,B_286)) = B_286
      | ~ m1_pre_topc(k1_pre_topc(A_285,B_286),A_285)
      | ~ v1_pre_topc(k1_pre_topc(A_285,B_286))
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6764,plain,
    ( k2_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = '#skF_1'('#skF_2','#skF_4')
    | ~ v1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_637,c_6754])).

tff(c_6784,plain,(
    k2_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_62,c_570,c_568,c_6764])).

tff(c_361,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_4',k2_struct_0('#skF_4')),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_352])).

tff(c_369,plain,(
    m1_pre_topc(k1_pre_topc('#skF_4',k2_struct_0('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_361])).

tff(c_398,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_4',k2_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_369,c_26])).

tff(c_401,plain,(
    l1_pre_topc(k1_pre_topc('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_398])).

tff(c_405,plain,(
    u1_struct_0(k1_pre_topc('#skF_4',k2_struct_0('#skF_4'))) = k2_struct_0(k1_pre_topc('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_401,c_85])).

tff(c_7104,plain,(
    u1_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6784,c_559,c_559,c_405])).

tff(c_153,plain,(
    ! [B_61] :
      ( r1_tarski(u1_struct_0(B_61),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_61,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_145])).

tff(c_168,plain,(
    ! [B_61] :
      ( r1_tarski(u1_struct_0(B_61),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_61,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_153])).

tff(c_7206,plain,
    ( r1_tarski('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7104,c_168])).

tff(c_7259,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6450,c_7206])).

tff(c_14015,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_4')
    | ~ l1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_13988,c_7259])).

tff(c_14055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_637,c_14015])).

tff(c_14056,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6448])).

tff(c_14409,plain,(
    ! [B_438] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_438),k2_struct_0('#skF_2'))
      | v1_tex_2(B_438,'#skF_2')
      | ~ m1_pre_topc(B_438,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_767])).

tff(c_14412,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_14056,c_14409])).

tff(c_14415,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14412])).

tff(c_14417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_14415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.43/3.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.43/3.62  
% 9.43/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.43/3.62  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.43/3.62  
% 9.43/3.62  %Foreground sorts:
% 9.43/3.62  
% 9.43/3.62  
% 9.43/3.62  %Background operators:
% 9.43/3.62  
% 9.43/3.62  
% 9.43/3.62  %Foreground operators:
% 9.43/3.62  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 9.43/3.62  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.43/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.43/3.62  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.43/3.62  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 9.43/3.62  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 9.43/3.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.43/3.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.43/3.62  tff('#skF_2', type, '#skF_2': $i).
% 9.43/3.62  tff('#skF_3', type, '#skF_3': $i).
% 9.43/3.62  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.43/3.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.43/3.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.43/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.43/3.62  tff('#skF_4', type, '#skF_4': $i).
% 9.43/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.43/3.62  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.43/3.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.43/3.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.43/3.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.43/3.62  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.43/3.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.43/3.62  
% 9.64/3.64  tff(f_141, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tex_2)).
% 9.64/3.64  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.64/3.64  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.64/3.64  tff(f_56, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 9.64/3.64  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 9.64/3.64  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 9.64/3.64  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.64/3.64  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 9.64/3.64  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 9.64/3.64  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 9.64/3.64  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.64/3.64  tff(f_126, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 9.64/3.64  tff(f_38, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 9.64/3.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.64/3.64  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 9.64/3.64  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 9.64/3.64  tff(c_50, plain, (~v1_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.64/3.64  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.64/3.64  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.64/3.64  tff(c_95, plain, (![B_55, A_56]: (l1_pre_topc(B_55) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.64/3.64  tff(c_98, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_95])).
% 9.64/3.64  tff(c_104, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_98])).
% 9.64/3.64  tff(c_24, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.64/3.64  tff(c_81, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.64/3.64  tff(c_85, plain, (![A_16]: (u1_struct_0(A_16)=k2_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_24, c_81])).
% 9.64/3.64  tff(c_118, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_104, c_85])).
% 9.64/3.64  tff(c_553, plain, (![B_86, A_87]: (u1_struct_0(B_86)='#skF_1'(A_87, B_86) | v1_tex_2(B_86, A_87) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.64/3.64  tff(c_556, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_553, c_50])).
% 9.64/3.64  tff(c_559, plain, (k2_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_118, c_556])).
% 9.64/3.64  tff(c_570, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_118])).
% 9.64/3.64  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.64/3.64  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.64/3.64  tff(c_62, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 9.64/3.64  tff(c_332, plain, (![A_74, B_75]: (m1_pre_topc(k1_pre_topc(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.64/3.64  tff(c_352, plain, (![A_76]: (m1_pre_topc(k1_pre_topc(A_76, u1_struct_0(A_76)), A_76) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_62, c_332])).
% 9.64/3.64  tff(c_26, plain, (![B_19, A_17]: (l1_pre_topc(B_19) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.64/3.64  tff(c_365, plain, (![A_76]: (l1_pre_topc(k1_pre_topc(A_76, u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_352, c_26])).
% 9.64/3.64  tff(c_596, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_570, c_365])).
% 9.64/3.64  tff(c_635, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_596])).
% 9.64/3.64  tff(c_351, plain, (![A_74]: (m1_pre_topc(k1_pre_topc(A_74, u1_struct_0(A_74)), A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_62, c_332])).
% 9.64/3.64  tff(c_599, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_570, c_351])).
% 9.64/3.64  tff(c_637, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_599])).
% 9.64/3.64  tff(c_687, plain, (![A_89, B_90]: (m1_pre_topc(A_89, g1_pre_topc(u1_struct_0(B_90), u1_pre_topc(B_90))) | ~m1_pre_topc(A_89, B_90) | ~l1_pre_topc(B_90) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.64/3.64  tff(c_696, plain, (![A_89]: (m1_pre_topc(A_89, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_89, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_89))), inference(superposition, [status(thm), theory('equality')], [c_570, c_687])).
% 9.64/3.64  tff(c_13953, plain, (![A_413]: (m1_pre_topc(A_413, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_413, '#skF_4') | ~l1_pre_topc(A_413))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_696])).
% 9.64/3.64  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.64/3.64  tff(c_101, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_95])).
% 9.64/3.64  tff(c_107, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_101])).
% 9.64/3.64  tff(c_122, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_107, c_85])).
% 9.64/3.64  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.64/3.64  tff(c_123, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_54])).
% 9.64/3.64  tff(c_132, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_123])).
% 9.64/3.64  tff(c_426, plain, (![B_78, A_79]: (m1_pre_topc(B_78, A_79) | ~m1_pre_topc(B_78, g1_pre_topc(u1_struct_0(A_79), u1_pre_topc(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.64/3.64  tff(c_433, plain, (![B_78]: (m1_pre_topc(B_78, '#skF_3') | ~m1_pre_topc(B_78, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_426])).
% 9.64/3.64  tff(c_442, plain, (![B_78]: (m1_pre_topc(B_78, '#skF_3') | ~m1_pre_topc(B_78, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_132, c_433])).
% 9.64/3.64  tff(c_6869, plain, (![B_78]: (m1_pre_topc(B_78, '#skF_3') | ~m1_pre_topc(B_78, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_442])).
% 9.64/3.64  tff(c_13988, plain, (![A_414]: (m1_pre_topc(A_414, '#skF_3') | ~m1_pre_topc(A_414, '#skF_4') | ~l1_pre_topc(A_414))), inference(resolution, [status(thm)], [c_13953, c_6869])).
% 9.64/3.64  tff(c_86, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_24, c_81])).
% 9.64/3.64  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_86])).
% 9.64/3.64  tff(c_263, plain, (![B_69, A_70]: (m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.64/3.64  tff(c_287, plain, (![B_69]: (m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_69, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_263])).
% 9.64/3.64  tff(c_507, plain, (![B_84]: (m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_84, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_287])).
% 9.64/3.64  tff(c_516, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_507])).
% 9.64/3.64  tff(c_524, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_516])).
% 9.64/3.64  tff(c_46, plain, (![B_43, A_42]: (v1_subset_1(B_43, A_42) | B_43=A_42 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.64/3.64  tff(c_533, plain, (v1_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_524, c_46])).
% 9.64/3.64  tff(c_6448, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_559, c_533])).
% 9.64/3.64  tff(c_6449, plain, (k2_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_6448])).
% 9.64/3.64  tff(c_12, plain, (![A_5]: (~v1_subset_1(k2_subset_1(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.64/3.64  tff(c_61, plain, (![A_5]: (~v1_subset_1(A_5, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 9.64/3.64  tff(c_52, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.64/3.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.64/3.64  tff(c_513, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_507])).
% 9.64/3.64  tff(c_522, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_513])).
% 9.64/3.64  tff(c_529, plain, (v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_522, c_46])).
% 9.64/3.64  tff(c_859, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_529])).
% 9.64/3.64  tff(c_1063, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_859, c_559, c_859, c_559, c_533])).
% 9.64/3.64  tff(c_1064, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_1063])).
% 9.64/3.64  tff(c_145, plain, (![B_61, A_62]: (r1_tarski(u1_struct_0(B_61), u1_struct_0(A_62)) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.64/3.64  tff(c_165, plain, (![B_61]: (r1_tarski(u1_struct_0(B_61), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_61, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_145])).
% 9.64/3.64  tff(c_239, plain, (![B_68]: (r1_tarski(u1_struct_0(B_68), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_68, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_165])).
% 9.64/3.64  tff(c_247, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_239])).
% 9.64/3.64  tff(c_255, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_247])).
% 9.64/3.64  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.64/3.64  tff(c_262, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_255, c_2])).
% 9.64/3.64  tff(c_1061, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), '#skF_1'('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_859, c_559, c_859, c_559, c_262])).
% 9.64/3.64  tff(c_1062, plain, (~r1_tarski(k2_struct_0('#skF_3'), '#skF_1'('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1061])).
% 9.64/3.64  tff(c_1086, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1064, c_1062])).
% 9.64/3.64  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1086])).
% 9.64/3.64  tff(c_1106, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1063])).
% 9.64/3.64  tff(c_758, plain, (![A_92, B_93]: (~v1_subset_1('#skF_1'(A_92, B_93), u1_struct_0(A_92)) | v1_tex_2(B_93, A_92) | ~m1_pre_topc(B_93, A_92) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.64/3.64  tff(c_767, plain, (![B_93]: (~v1_subset_1('#skF_1'('#skF_2', B_93), k2_struct_0('#skF_2')) | v1_tex_2(B_93, '#skF_2') | ~m1_pre_topc(B_93, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_758])).
% 9.64/3.64  tff(c_773, plain, (![B_93]: (~v1_subset_1('#skF_1'('#skF_2', B_93), k2_struct_0('#skF_2')) | v1_tex_2(B_93, '#skF_2') | ~m1_pre_topc(B_93, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_767])).
% 9.64/3.64  tff(c_2797, plain, (![B_164]: (~v1_subset_1('#skF_1'('#skF_2', B_164), k2_struct_0('#skF_3')) | v1_tex_2(B_164, '#skF_2') | ~m1_pre_topc(B_164, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_859, c_773])).
% 9.64/3.64  tff(c_2800, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1106, c_2797])).
% 9.64/3.64  tff(c_2803, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2800])).
% 9.64/3.64  tff(c_2805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_2803])).
% 9.64/3.64  tff(c_2806, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_1061])).
% 9.64/3.64  tff(c_2823, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2806, c_122])).
% 9.64/3.64  tff(c_901, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_859, c_90])).
% 9.64/3.64  tff(c_2812, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2806, c_901])).
% 9.64/3.64  tff(c_34, plain, (![B_28, A_26]: (m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.64/3.64  tff(c_3036, plain, (![B_165, A_166]: (v1_subset_1(u1_struct_0(B_165), u1_struct_0(A_166)) | ~m1_subset_1(u1_struct_0(B_165), k1_zfmisc_1(u1_struct_0(A_166))) | ~v1_tex_2(B_165, A_166) | ~m1_pre_topc(B_165, A_166) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.64/3.64  tff(c_3539, plain, (![B_195, A_196]: (v1_subset_1(u1_struct_0(B_195), u1_struct_0(A_196)) | ~v1_tex_2(B_195, A_196) | ~m1_pre_topc(B_195, A_196) | ~l1_pre_topc(A_196))), inference(resolution, [status(thm)], [c_34, c_3036])).
% 9.64/3.64  tff(c_3555, plain, (![B_195]: (v1_subset_1(u1_struct_0(B_195), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2(B_195, '#skF_2') | ~m1_pre_topc(B_195, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2812, c_3539])).
% 9.64/3.64  tff(c_6385, plain, (![B_267]: (v1_subset_1(u1_struct_0(B_267), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2(B_267, '#skF_2') | ~m1_pre_topc(B_267, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3555])).
% 9.64/3.64  tff(c_6400, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2823, c_6385])).
% 9.64/3.64  tff(c_6413, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_6400])).
% 9.64/3.64  tff(c_6415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_6413])).
% 9.64/3.64  tff(c_6417, plain, (k2_struct_0('#skF_2')!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_529])).
% 9.64/3.64  tff(c_244, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_239])).
% 9.64/3.64  tff(c_253, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_244])).
% 9.64/3.64  tff(c_259, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_253, c_2])).
% 9.64/3.64  tff(c_6447, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_6417, c_259])).
% 9.64/3.64  tff(c_6450, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6449, c_6447])).
% 9.64/3.64  tff(c_201, plain, (![A_65, B_66]: (v1_pre_topc(k1_pre_topc(A_65, B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.64/3.64  tff(c_222, plain, (![A_67]: (v1_pre_topc(k1_pre_topc(A_67, u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_62, c_201])).
% 9.64/3.64  tff(c_228, plain, (v1_pre_topc(k1_pre_topc('#skF_4', k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_118, c_222])).
% 9.64/3.64  tff(c_235, plain, (v1_pre_topc(k1_pre_topc('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_228])).
% 9.64/3.64  tff(c_568, plain, (v1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_235])).
% 9.64/3.64  tff(c_6754, plain, (![A_285, B_286]: (k2_struct_0(k1_pre_topc(A_285, B_286))=B_286 | ~m1_pre_topc(k1_pre_topc(A_285, B_286), A_285) | ~v1_pre_topc(k1_pre_topc(A_285, B_286)) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.64/3.64  tff(c_6764, plain, (k2_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))='#skF_1'('#skF_2', '#skF_4') | ~v1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_637, c_6754])).
% 9.64/3.64  tff(c_6784, plain, (k2_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_62, c_570, c_568, c_6764])).
% 9.64/3.64  tff(c_361, plain, (m1_pre_topc(k1_pre_topc('#skF_4', k2_struct_0('#skF_4')), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_118, c_352])).
% 9.64/3.64  tff(c_369, plain, (m1_pre_topc(k1_pre_topc('#skF_4', k2_struct_0('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_361])).
% 9.64/3.64  tff(c_398, plain, (l1_pre_topc(k1_pre_topc('#skF_4', k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_369, c_26])).
% 9.64/3.64  tff(c_401, plain, (l1_pre_topc(k1_pre_topc('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_398])).
% 9.64/3.64  tff(c_405, plain, (u1_struct_0(k1_pre_topc('#skF_4', k2_struct_0('#skF_4')))=k2_struct_0(k1_pre_topc('#skF_4', k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_401, c_85])).
% 9.64/3.64  tff(c_7104, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6784, c_559, c_559, c_405])).
% 9.64/3.64  tff(c_153, plain, (![B_61]: (r1_tarski(u1_struct_0(B_61), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_61, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_145])).
% 9.64/3.64  tff(c_168, plain, (![B_61]: (r1_tarski(u1_struct_0(B_61), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_61, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_153])).
% 9.64/3.64  tff(c_7206, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7104, c_168])).
% 9.64/3.64  tff(c_7259, plain, (~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_6450, c_7206])).
% 9.64/3.64  tff(c_14015, plain, (~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_4') | ~l1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_13988, c_7259])).
% 9.64/3.64  tff(c_14055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_635, c_637, c_14015])).
% 9.64/3.64  tff(c_14056, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_6448])).
% 9.64/3.64  tff(c_14409, plain, (![B_438]: (~v1_subset_1('#skF_1'('#skF_2', B_438), k2_struct_0('#skF_2')) | v1_tex_2(B_438, '#skF_2') | ~m1_pre_topc(B_438, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_767])).
% 9.64/3.64  tff(c_14412, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_14056, c_14409])).
% 9.64/3.64  tff(c_14415, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14412])).
% 9.64/3.64  tff(c_14417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_14415])).
% 9.64/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.64/3.64  
% 9.64/3.64  Inference rules
% 9.64/3.64  ----------------------
% 9.64/3.64  #Ref     : 0
% 9.64/3.64  #Sup     : 3117
% 9.64/3.64  #Fact    : 0
% 9.64/3.64  #Define  : 0
% 9.64/3.64  #Split   : 19
% 9.64/3.64  #Chain   : 0
% 9.64/3.64  #Close   : 0
% 9.64/3.64  
% 9.64/3.64  Ordering : KBO
% 9.64/3.64  
% 9.64/3.64  Simplification rules
% 9.64/3.64  ----------------------
% 9.64/3.64  #Subsume      : 469
% 9.64/3.64  #Demod        : 4381
% 9.64/3.64  #Tautology    : 1050
% 9.64/3.64  #SimpNegUnit  : 244
% 9.64/3.64  #BackRed      : 81
% 9.64/3.64  
% 9.64/3.64  #Partial instantiations: 0
% 9.64/3.64  #Strategies tried      : 1
% 9.64/3.64  
% 9.64/3.64  Timing (in seconds)
% 9.64/3.64  ----------------------
% 9.64/3.64  Preprocessing        : 0.33
% 9.64/3.64  Parsing              : 0.17
% 9.64/3.64  CNF conversion       : 0.02
% 9.64/3.64  Main loop            : 2.48
% 9.64/3.64  Inferencing          : 0.66
% 9.64/3.64  Reduction            : 1.04
% 9.64/3.64  Demodulation         : 0.77
% 9.64/3.64  BG Simplification    : 0.07
% 9.64/3.64  Subsumption          : 0.55
% 9.64/3.64  Abstraction          : 0.10
% 9.64/3.65  MUC search           : 0.00
% 9.64/3.65  Cooper               : 0.00
% 9.64/3.65  Total                : 2.86
% 9.64/3.65  Index Insertion      : 0.00
% 9.64/3.65  Index Deletion       : 0.00
% 9.64/3.65  Index Matching       : 0.00
% 9.64/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
