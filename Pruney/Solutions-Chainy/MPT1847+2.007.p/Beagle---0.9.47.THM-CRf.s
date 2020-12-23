%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:53 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 930 expanded)
%              Number of leaves         :   36 ( 336 expanded)
%              Depth                    :   20
%              Number of atoms          :  242 (2753 expanded)
%              Number of equality atoms :   27 ( 361 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_10] : ~ v1_subset_1(k2_subset_1(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    ! [A_10] : ~ v1_subset_1(A_10,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    ! [A_25] :
      ( m1_pre_topc(A_25,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    ! [B_32,A_26] :
      ( u1_struct_0(B_32) = '#skF_3'(A_26,B_32)
      | v1_tex_2(B_32,A_26)
      | ~ m1_pre_topc(B_32,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    ! [B_24,A_22] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_481,plain,(
    ! [B_105,A_106] :
      ( v1_subset_1(u1_struct_0(B_105),u1_struct_0(A_106))
      | ~ m1_subset_1(u1_struct_0(B_105),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v1_tex_2(B_105,A_106)
      | ~ m1_pre_topc(B_105,A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_495,plain,(
    ! [B_107,A_108] :
      ( v1_subset_1(u1_struct_0(B_107),u1_struct_0(A_108))
      | ~ v1_tex_2(B_107,A_108)
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_36,c_481])).

tff(c_509,plain,(
    ! [A_109] :
      ( ~ v1_tex_2(A_109,A_109)
      | ~ m1_pre_topc(A_109,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_495,c_63])).

tff(c_515,plain,(
    ! [A_110] :
      ( u1_struct_0(A_110) = '#skF_3'(A_110,A_110)
      | ~ m1_pre_topc(A_110,A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_44,c_509])).

tff(c_717,plain,(
    ! [A_112] :
      ( u1_struct_0(A_112) = '#skF_3'(A_112,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_38,c_515])).

tff(c_728,plain,(
    u1_struct_0('#skF_4') = '#skF_3'('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_717])).

tff(c_406,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1('#skF_3'(A_96,B_97),k1_zfmisc_1(u1_struct_0(A_96)))
      | v1_tex_2(B_97,A_96)
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [B_37,A_36] :
      ( v1_subset_1(B_37,A_36)
      | B_37 = A_36
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1549,plain,(
    ! [A_139,B_140] :
      ( v1_subset_1('#skF_3'(A_139,B_140),u1_struct_0(A_139))
      | u1_struct_0(A_139) = '#skF_3'(A_139,B_140)
      | v1_tex_2(B_140,A_139)
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_406,c_48])).

tff(c_42,plain,(
    ! [A_26,B_32] :
      ( ~ v1_subset_1('#skF_3'(A_26,B_32),u1_struct_0(A_26))
      | v1_tex_2(B_32,A_26)
      | ~ m1_pre_topc(B_32,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1624,plain,(
    ! [A_142,B_143] :
      ( u1_struct_0(A_142) = '#skF_3'(A_142,B_143)
      | v1_tex_2(B_143,A_142)
      | ~ m1_pre_topc(B_143,A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_1549,c_42])).

tff(c_52,plain,(
    ~ v1_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1646,plain,
    ( u1_struct_0('#skF_4') = '#skF_3'('#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1624,c_52])).

tff(c_1665,plain,(
    '#skF_3'('#skF_4','#skF_6') = '#skF_3'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_728,c_1646])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_54,plain,(
    v1_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_88,plain,(
    ! [B_51,A_52] :
      ( l1_pre_topc(B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_97])).

tff(c_162,plain,(
    ! [B_72,A_73] :
      ( u1_struct_0(B_72) = '#skF_3'(A_73,B_72)
      | v1_tex_2(B_72,A_73)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_165,plain,
    ( u1_struct_0('#skF_6') = '#skF_3'('#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_52])).

tff(c_168,plain,(
    u1_struct_0('#skF_6') = '#skF_3'('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_165])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_170,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_56])).

tff(c_313,plain,(
    ! [A_87,B_88] :
      ( m1_pre_topc(A_87,g1_pre_topc(u1_struct_0(B_88),u1_pre_topc(B_88)))
      | ~ m1_pre_topc(A_87,B_88)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_322,plain,(
    ! [A_87] :
      ( m1_pre_topc(A_87,g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6')))
      | ~ m1_pre_topc(A_87,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_313])).

tff(c_332,plain,(
    ! [A_89] :
      ( m1_pre_topc(A_89,g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6')))
      | ~ m1_pre_topc(A_89,'#skF_5')
      | ~ l1_pre_topc(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_322])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_88])).

tff(c_101,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_94])).

tff(c_30,plain,(
    ! [B_18,A_16] :
      ( m1_pre_topc(B_18,A_16)
      | ~ m1_pre_topc(B_18,g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_174,plain,(
    ! [B_18] :
      ( m1_pre_topc(B_18,'#skF_6')
      | ~ m1_pre_topc(B_18,g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_30])).

tff(c_190,plain,(
    ! [B_18] :
      ( m1_pre_topc(B_18,'#skF_6')
      | ~ m1_pre_topc(B_18,g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_174])).

tff(c_345,plain,(
    ! [A_90] :
      ( m1_pre_topc(A_90,'#skF_6')
      | ~ m1_pre_topc(A_90,'#skF_5')
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_332,c_190])).

tff(c_349,plain,
    ( m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_345])).

tff(c_352,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_349])).

tff(c_325,plain,(
    ! [A_87] :
      ( m1_pre_topc(A_87,g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6')))
      | ~ m1_pre_topc(A_87,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_313])).

tff(c_359,plain,(
    ! [A_91] :
      ( m1_pre_topc(A_91,g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6')))
      | ~ m1_pre_topc(A_91,'#skF_6')
      | ~ l1_pre_topc(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_325])).

tff(c_135,plain,(
    ! [B_65,A_66] :
      ( m1_pre_topc(B_65,A_66)
      | ~ m1_pre_topc(B_65,g1_pre_topc(u1_struct_0(A_66),u1_pre_topc(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_142,plain,(
    ! [B_65] :
      ( m1_pre_topc(B_65,'#skF_5')
      | ~ m1_pre_topc(B_65,g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_135])).

tff(c_145,plain,(
    ! [B_65] :
      ( m1_pre_topc(B_65,'#skF_5')
      | ~ m1_pre_topc(B_65,g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_142])).

tff(c_169,plain,(
    ! [B_65] :
      ( m1_pre_topc(B_65,'#skF_5')
      | ~ m1_pre_topc(B_65,g1_pre_topc('#skF_3'('#skF_4','#skF_6'),u1_pre_topc('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_145])).

tff(c_370,plain,(
    ! [A_91] :
      ( m1_pre_topc(A_91,'#skF_5')
      | ~ m1_pre_topc(A_91,'#skF_6')
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_359,c_169])).

tff(c_519,plain,
    ( u1_struct_0('#skF_5') = '#skF_3'('#skF_5','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_370,c_515])).

tff(c_540,plain,(
    u1_struct_0('#skF_5') = '#skF_3'('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_352,c_519])).

tff(c_122,plain,(
    ! [B_61,A_62] :
      ( m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_109,plain,(
    ! [A_53,A_3] :
      ( r1_tarski(A_53,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_112,plain,(
    ! [A_53,A_3] :
      ( r1_tarski(A_53,A_3)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_109])).

tff(c_130,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(u1_struct_0(B_61),u1_struct_0(A_62))
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_122,c_112])).

tff(c_180,plain,(
    ! [B_61] :
      ( r1_tarski(u1_struct_0(B_61),'#skF_3'('#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_61,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_130])).

tff(c_192,plain,(
    ! [B_61] :
      ( r1_tarski(u1_struct_0(B_61),'#skF_3'('#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_61,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_180])).

tff(c_621,plain,
    ( r1_tarski('#skF_3'('#skF_5','#skF_5'),'#skF_3'('#skF_4','#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_192])).

tff(c_668,plain,(
    r1_tarski('#skF_3'('#skF_5','#skF_5'),'#skF_3'('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_621])).

tff(c_186,plain,(
    ! [B_24] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1('#skF_3'('#skF_4','#skF_6')))
      | ~ m1_pre_topc(B_24,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_36])).

tff(c_213,plain,(
    ! [B_75] :
      ( m1_subset_1(u1_struct_0(B_75),k1_zfmisc_1('#skF_3'('#skF_4','#skF_6')))
      | ~ m1_pre_topc(B_75,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_186])).

tff(c_222,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_6'),k1_zfmisc_1('#skF_3'('#skF_4','#skF_6')))
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_213])).

tff(c_252,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_255,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_255])).

tff(c_261,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_177,plain,(
    ! [A_62] :
      ( r1_tarski('#skF_3'('#skF_4','#skF_6'),u1_struct_0(A_62))
      | ~ m1_pre_topc('#skF_6',A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_130])).

tff(c_615,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_6'),'#skF_3'('#skF_5','#skF_5'))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_177])).

tff(c_664,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_6'),'#skF_3'('#skF_5','#skF_5'))
    | ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_615])).

tff(c_968,plain,(
    ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_971,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_370,c_968])).

tff(c_975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_261,c_971])).

tff(c_976,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_6'),'#skF_3'('#skF_5','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_998,plain,
    ( '#skF_3'('#skF_5','#skF_5') = '#skF_3'('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3'('#skF_5','#skF_5'),'#skF_3'('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_976,c_2])).

tff(c_1001,plain,(
    '#skF_3'('#skF_5','#skF_5') = '#skF_3'('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_998])).

tff(c_1008,plain,(
    u1_struct_0('#skF_5') = '#skF_3'('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_540])).

tff(c_494,plain,(
    ! [B_24,A_22] :
      ( v1_subset_1(u1_struct_0(B_24),u1_struct_0(A_22))
      | ~ v1_tex_2(B_24,A_22)
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_36,c_481])).

tff(c_739,plain,(
    ! [B_24] :
      ( v1_subset_1(u1_struct_0(B_24),'#skF_3'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_24,'#skF_4')
      | ~ m1_pre_topc(B_24,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_494])).

tff(c_1526,plain,(
    ! [B_138] :
      ( v1_subset_1(u1_struct_0(B_138),'#skF_3'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_138,'#skF_4')
      | ~ m1_pre_topc(B_138,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_739])).

tff(c_1529,plain,
    ( v1_subset_1('#skF_3'('#skF_4','#skF_6'),'#skF_3'('#skF_4','#skF_4'))
    | ~ v1_tex_2('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_1526])).

tff(c_1537,plain,(
    v1_subset_1('#skF_3'('#skF_4','#skF_6'),'#skF_3'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_1529])).

tff(c_1666,plain,(
    v1_subset_1('#skF_3'('#skF_4','#skF_4'),'#skF_3'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1537])).

tff(c_1699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_1666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.69  
% 3.35/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.69  %$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.35/1.69  
% 3.35/1.69  %Foreground sorts:
% 3.35/1.69  
% 3.35/1.69  
% 3.35/1.69  %Background operators:
% 3.35/1.69  
% 3.35/1.69  
% 3.35/1.69  %Foreground operators:
% 3.35/1.69  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.35/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.69  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.35/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.69  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.35/1.69  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.35/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.35/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.35/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.35/1.69  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.35/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.35/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.69  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.35/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.69  
% 3.66/1.71  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.66/1.71  tff(f_46, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.66/1.71  tff(f_122, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 3.66/1.71  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.66/1.71  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.66/1.71  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.66/1.71  tff(f_107, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.66/1.71  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.66/1.71  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.66/1.71  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.66/1.71  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.66/1.71  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.66/1.71  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.66/1.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.66/1.71  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.66/1.71  tff(c_24, plain, (![A_10]: (~v1_subset_1(k2_subset_1(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.66/1.71  tff(c_63, plain, (![A_10]: (~v1_subset_1(A_10, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 3.66/1.71  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.66/1.71  tff(c_58, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.66/1.71  tff(c_38, plain, (![A_25]: (m1_pre_topc(A_25, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.66/1.71  tff(c_44, plain, (![B_32, A_26]: (u1_struct_0(B_32)='#skF_3'(A_26, B_32) | v1_tex_2(B_32, A_26) | ~m1_pre_topc(B_32, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.66/1.71  tff(c_36, plain, (![B_24, A_22]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.66/1.71  tff(c_481, plain, (![B_105, A_106]: (v1_subset_1(u1_struct_0(B_105), u1_struct_0(A_106)) | ~m1_subset_1(u1_struct_0(B_105), k1_zfmisc_1(u1_struct_0(A_106))) | ~v1_tex_2(B_105, A_106) | ~m1_pre_topc(B_105, A_106) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.66/1.71  tff(c_495, plain, (![B_107, A_108]: (v1_subset_1(u1_struct_0(B_107), u1_struct_0(A_108)) | ~v1_tex_2(B_107, A_108) | ~m1_pre_topc(B_107, A_108) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_36, c_481])).
% 3.66/1.71  tff(c_509, plain, (![A_109]: (~v1_tex_2(A_109, A_109) | ~m1_pre_topc(A_109, A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_495, c_63])).
% 3.66/1.71  tff(c_515, plain, (![A_110]: (u1_struct_0(A_110)='#skF_3'(A_110, A_110) | ~m1_pre_topc(A_110, A_110) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_44, c_509])).
% 3.66/1.71  tff(c_717, plain, (![A_112]: (u1_struct_0(A_112)='#skF_3'(A_112, A_112) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_38, c_515])).
% 3.66/1.71  tff(c_728, plain, (u1_struct_0('#skF_4')='#skF_3'('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_717])).
% 3.66/1.71  tff(c_406, plain, (![A_96, B_97]: (m1_subset_1('#skF_3'(A_96, B_97), k1_zfmisc_1(u1_struct_0(A_96))) | v1_tex_2(B_97, A_96) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.66/1.71  tff(c_48, plain, (![B_37, A_36]: (v1_subset_1(B_37, A_36) | B_37=A_36 | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.66/1.71  tff(c_1549, plain, (![A_139, B_140]: (v1_subset_1('#skF_3'(A_139, B_140), u1_struct_0(A_139)) | u1_struct_0(A_139)='#skF_3'(A_139, B_140) | v1_tex_2(B_140, A_139) | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_406, c_48])).
% 3.66/1.71  tff(c_42, plain, (![A_26, B_32]: (~v1_subset_1('#skF_3'(A_26, B_32), u1_struct_0(A_26)) | v1_tex_2(B_32, A_26) | ~m1_pre_topc(B_32, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.66/1.71  tff(c_1624, plain, (![A_142, B_143]: (u1_struct_0(A_142)='#skF_3'(A_142, B_143) | v1_tex_2(B_143, A_142) | ~m1_pre_topc(B_143, A_142) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_1549, c_42])).
% 3.66/1.71  tff(c_52, plain, (~v1_tex_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.66/1.71  tff(c_1646, plain, (u1_struct_0('#skF_4')='#skF_3'('#skF_4', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1624, c_52])).
% 3.66/1.71  tff(c_1665, plain, ('#skF_3'('#skF_4', '#skF_6')='#skF_3'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_728, c_1646])).
% 3.66/1.71  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.66/1.71  tff(c_54, plain, (v1_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.66/1.71  tff(c_88, plain, (![B_51, A_52]: (l1_pre_topc(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.71  tff(c_97, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_88])).
% 3.66/1.71  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_97])).
% 3.66/1.71  tff(c_162, plain, (![B_72, A_73]: (u1_struct_0(B_72)='#skF_3'(A_73, B_72) | v1_tex_2(B_72, A_73) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.66/1.71  tff(c_165, plain, (u1_struct_0('#skF_6')='#skF_3'('#skF_4', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_162, c_52])).
% 3.66/1.71  tff(c_168, plain, (u1_struct_0('#skF_6')='#skF_3'('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_165])).
% 3.66/1.71  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))=g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.66/1.71  tff(c_170, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))=g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_56])).
% 3.66/1.71  tff(c_313, plain, (![A_87, B_88]: (m1_pre_topc(A_87, g1_pre_topc(u1_struct_0(B_88), u1_pre_topc(B_88))) | ~m1_pre_topc(A_87, B_88) | ~l1_pre_topc(B_88) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.66/1.71  tff(c_322, plain, (![A_87]: (m1_pre_topc(A_87, g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))) | ~m1_pre_topc(A_87, '#skF_5') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_87))), inference(superposition, [status(thm), theory('equality')], [c_170, c_313])).
% 3.66/1.71  tff(c_332, plain, (![A_89]: (m1_pre_topc(A_89, g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))) | ~m1_pre_topc(A_89, '#skF_5') | ~l1_pre_topc(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_322])).
% 3.66/1.71  tff(c_94, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_88])).
% 3.66/1.71  tff(c_101, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_94])).
% 3.66/1.71  tff(c_30, plain, (![B_18, A_16]: (m1_pre_topc(B_18, A_16) | ~m1_pre_topc(B_18, g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.71  tff(c_174, plain, (![B_18]: (m1_pre_topc(B_18, '#skF_6') | ~m1_pre_topc(B_18, g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_30])).
% 3.66/1.71  tff(c_190, plain, (![B_18]: (m1_pre_topc(B_18, '#skF_6') | ~m1_pre_topc(B_18, g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_174])).
% 3.66/1.71  tff(c_345, plain, (![A_90]: (m1_pre_topc(A_90, '#skF_6') | ~m1_pre_topc(A_90, '#skF_5') | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_332, c_190])).
% 3.66/1.71  tff(c_349, plain, (m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_345])).
% 3.66/1.71  tff(c_352, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_349])).
% 3.66/1.71  tff(c_325, plain, (![A_87]: (m1_pre_topc(A_87, g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))) | ~m1_pre_topc(A_87, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_87))), inference(superposition, [status(thm), theory('equality')], [c_168, c_313])).
% 3.66/1.71  tff(c_359, plain, (![A_91]: (m1_pre_topc(A_91, g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))) | ~m1_pre_topc(A_91, '#skF_6') | ~l1_pre_topc(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_325])).
% 3.66/1.71  tff(c_135, plain, (![B_65, A_66]: (m1_pre_topc(B_65, A_66) | ~m1_pre_topc(B_65, g1_pre_topc(u1_struct_0(A_66), u1_pre_topc(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.71  tff(c_142, plain, (![B_65]: (m1_pre_topc(B_65, '#skF_5') | ~m1_pre_topc(B_65, g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_135])).
% 3.66/1.71  tff(c_145, plain, (![B_65]: (m1_pre_topc(B_65, '#skF_5') | ~m1_pre_topc(B_65, g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_142])).
% 3.66/1.71  tff(c_169, plain, (![B_65]: (m1_pre_topc(B_65, '#skF_5') | ~m1_pre_topc(B_65, g1_pre_topc('#skF_3'('#skF_4', '#skF_6'), u1_pre_topc('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_145])).
% 3.66/1.71  tff(c_370, plain, (![A_91]: (m1_pre_topc(A_91, '#skF_5') | ~m1_pre_topc(A_91, '#skF_6') | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_359, c_169])).
% 3.66/1.71  tff(c_519, plain, (u1_struct_0('#skF_5')='#skF_3'('#skF_5', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_370, c_515])).
% 3.66/1.71  tff(c_540, plain, (u1_struct_0('#skF_5')='#skF_3'('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_352, c_519])).
% 3.66/1.71  tff(c_122, plain, (![B_61, A_62]: (m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.66/1.71  tff(c_22, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.71  tff(c_105, plain, (![A_53, B_54]: (r2_hidden(A_53, B_54) | v1_xboole_0(B_54) | ~m1_subset_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.66/1.71  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.66/1.71  tff(c_109, plain, (![A_53, A_3]: (r1_tarski(A_53, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_53, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_105, c_8])).
% 3.66/1.71  tff(c_112, plain, (![A_53, A_3]: (r1_tarski(A_53, A_3) | ~m1_subset_1(A_53, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_22, c_109])).
% 3.66/1.71  tff(c_130, plain, (![B_61, A_62]: (r1_tarski(u1_struct_0(B_61), u1_struct_0(A_62)) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_122, c_112])).
% 3.66/1.71  tff(c_180, plain, (![B_61]: (r1_tarski(u1_struct_0(B_61), '#skF_3'('#skF_4', '#skF_6')) | ~m1_pre_topc(B_61, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_130])).
% 3.66/1.71  tff(c_192, plain, (![B_61]: (r1_tarski(u1_struct_0(B_61), '#skF_3'('#skF_4', '#skF_6')) | ~m1_pre_topc(B_61, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_180])).
% 3.66/1.71  tff(c_621, plain, (r1_tarski('#skF_3'('#skF_5', '#skF_5'), '#skF_3'('#skF_4', '#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_540, c_192])).
% 3.66/1.71  tff(c_668, plain, (r1_tarski('#skF_3'('#skF_5', '#skF_5'), '#skF_3'('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_621])).
% 3.66/1.71  tff(c_186, plain, (![B_24]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1('#skF_3'('#skF_4', '#skF_6'))) | ~m1_pre_topc(B_24, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_36])).
% 3.66/1.71  tff(c_213, plain, (![B_75]: (m1_subset_1(u1_struct_0(B_75), k1_zfmisc_1('#skF_3'('#skF_4', '#skF_6'))) | ~m1_pre_topc(B_75, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_186])).
% 3.66/1.71  tff(c_222, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_3'('#skF_4', '#skF_6'))) | ~m1_pre_topc('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_168, c_213])).
% 3.66/1.71  tff(c_252, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_222])).
% 3.66/1.71  tff(c_255, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_38, c_252])).
% 3.66/1.71  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_255])).
% 3.66/1.71  tff(c_261, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_222])).
% 3.66/1.71  tff(c_177, plain, (![A_62]: (r1_tarski('#skF_3'('#skF_4', '#skF_6'), u1_struct_0(A_62)) | ~m1_pre_topc('#skF_6', A_62) | ~l1_pre_topc(A_62))), inference(superposition, [status(thm), theory('equality')], [c_168, c_130])).
% 3.66/1.71  tff(c_615, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_6'), '#skF_3'('#skF_5', '#skF_5')) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_540, c_177])).
% 3.66/1.71  tff(c_664, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_6'), '#skF_3'('#skF_5', '#skF_5')) | ~m1_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_615])).
% 3.66/1.71  tff(c_968, plain, (~m1_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_664])).
% 3.66/1.71  tff(c_971, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_370, c_968])).
% 3.66/1.71  tff(c_975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_261, c_971])).
% 3.66/1.71  tff(c_976, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_6'), '#skF_3'('#skF_5', '#skF_5'))), inference(splitRight, [status(thm)], [c_664])).
% 3.66/1.71  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.71  tff(c_998, plain, ('#skF_3'('#skF_5', '#skF_5')='#skF_3'('#skF_4', '#skF_6') | ~r1_tarski('#skF_3'('#skF_5', '#skF_5'), '#skF_3'('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_976, c_2])).
% 3.66/1.71  tff(c_1001, plain, ('#skF_3'('#skF_5', '#skF_5')='#skF_3'('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_668, c_998])).
% 3.66/1.71  tff(c_1008, plain, (u1_struct_0('#skF_5')='#skF_3'('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_540])).
% 3.66/1.71  tff(c_494, plain, (![B_24, A_22]: (v1_subset_1(u1_struct_0(B_24), u1_struct_0(A_22)) | ~v1_tex_2(B_24, A_22) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_36, c_481])).
% 3.66/1.71  tff(c_739, plain, (![B_24]: (v1_subset_1(u1_struct_0(B_24), '#skF_3'('#skF_4', '#skF_4')) | ~v1_tex_2(B_24, '#skF_4') | ~m1_pre_topc(B_24, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_728, c_494])).
% 3.66/1.71  tff(c_1526, plain, (![B_138]: (v1_subset_1(u1_struct_0(B_138), '#skF_3'('#skF_4', '#skF_4')) | ~v1_tex_2(B_138, '#skF_4') | ~m1_pre_topc(B_138, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_739])).
% 3.66/1.71  tff(c_1529, plain, (v1_subset_1('#skF_3'('#skF_4', '#skF_6'), '#skF_3'('#skF_4', '#skF_4')) | ~v1_tex_2('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1008, c_1526])).
% 3.66/1.71  tff(c_1537, plain, (v1_subset_1('#skF_3'('#skF_4', '#skF_6'), '#skF_3'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_1529])).
% 3.66/1.71  tff(c_1666, plain, (v1_subset_1('#skF_3'('#skF_4', '#skF_4'), '#skF_3'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1537])).
% 3.66/1.71  tff(c_1699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_1666])).
% 3.66/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.71  
% 3.66/1.71  Inference rules
% 3.66/1.71  ----------------------
% 3.66/1.71  #Ref     : 0
% 3.66/1.71  #Sup     : 321
% 3.66/1.71  #Fact    : 0
% 3.66/1.71  #Define  : 0
% 3.66/1.71  #Split   : 7
% 3.66/1.71  #Chain   : 0
% 3.66/1.71  #Close   : 0
% 3.66/1.71  
% 3.66/1.71  Ordering : KBO
% 3.66/1.71  
% 3.66/1.71  Simplification rules
% 3.66/1.71  ----------------------
% 3.66/1.72  #Subsume      : 63
% 3.66/1.72  #Demod        : 409
% 3.66/1.72  #Tautology    : 113
% 3.66/1.72  #SimpNegUnit  : 40
% 3.66/1.72  #BackRed      : 43
% 3.66/1.72  
% 3.66/1.72  #Partial instantiations: 0
% 3.66/1.72  #Strategies tried      : 1
% 3.66/1.72  
% 3.66/1.72  Timing (in seconds)
% 3.66/1.72  ----------------------
% 3.66/1.72  Preprocessing        : 0.32
% 3.66/1.72  Parsing              : 0.17
% 3.66/1.72  CNF conversion       : 0.03
% 3.66/1.72  Main loop            : 0.51
% 3.66/1.72  Inferencing          : 0.17
% 3.66/1.72  Reduction            : 0.17
% 3.66/1.72  Demodulation         : 0.12
% 3.66/1.72  BG Simplification    : 0.02
% 3.66/1.72  Subsumption          : 0.11
% 3.66/1.72  Abstraction          : 0.02
% 3.66/1.72  MUC search           : 0.00
% 3.66/1.72  Cooper               : 0.00
% 3.66/1.72  Total                : 0.88
% 3.66/1.72  Index Insertion      : 0.00
% 3.66/1.72  Index Deletion       : 0.00
% 3.66/1.72  Index Matching       : 0.00
% 3.66/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
