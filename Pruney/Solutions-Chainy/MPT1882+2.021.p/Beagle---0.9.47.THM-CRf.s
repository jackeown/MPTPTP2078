%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:15 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 387 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1455 expanded)
%              Number of equality atoms :   21 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_mcart_1 > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_107,plain,(
    ! [A_82,B_83] :
      ( '#skF_2'(A_82,B_83) != B_83
      | v3_tex_2(B_83,A_82)
      | ~ v2_tex_2(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_114,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_107])).

tff(c_118,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_114])).

tff(c_119,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_118])).

tff(c_120,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_179,plain,(
    ! [B_94,A_95] :
      ( v2_tex_2(B_94,A_95)
      | ~ v1_zfmisc_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_94)
      | ~ l1_pre_topc(A_95)
      | ~ v2_tdlat_3(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_189,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_179])).

tff(c_194,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_56,c_189])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_120,c_194])).

tff(c_197,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_198,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_199,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(B_96,'#skF_2'(A_97,B_96))
      | v3_tex_2(B_96,A_97)
      | ~ v2_tex_2(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_199])).

tff(c_208,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_198,c_204])).

tff(c_209,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_208])).

tff(c_30,plain,(
    ! [B_40,A_38] :
      ( B_40 = A_38
      | ~ r1_tarski(A_38,B_40)
      | ~ v1_zfmisc_1(B_40)
      | v1_xboole_0(B_40)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_212,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_209,c_30])).

tff(c_218,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_197,c_212])).

tff(c_222,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_226,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_222])).

tff(c_228,plain,(
    ! [A_100,B_101] :
      ( v2_tex_2('#skF_2'(A_100,B_101),A_100)
      | v3_tex_2(B_101,A_100)
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_233,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_237,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_198,c_233])).

tff(c_238,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_237])).

tff(c_265,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1('#skF_2'(A_106,B_107),k1_zfmisc_1(u1_struct_0(A_106)))
      | v3_tex_2(B_107,A_106)
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [B_43,A_41] :
      ( v1_zfmisc_1(B_43)
      | ~ v2_tex_2(B_43,A_41)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | v1_xboole_0(B_43)
      | ~ l1_pre_topc(A_41)
      | ~ v2_tdlat_3(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_373,plain,(
    ! [A_133,B_134] :
      ( v1_zfmisc_1('#skF_2'(A_133,B_134))
      | ~ v2_tex_2('#skF_2'(A_133,B_134),A_133)
      | v1_xboole_0('#skF_2'(A_133,B_134))
      | ~ v2_tdlat_3(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133)
      | v3_tex_2(B_134,A_133)
      | ~ v2_tex_2(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_265,c_34])).

tff(c_379,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_373])).

tff(c_386,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_198,c_44,c_42,c_379])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_226,c_222,c_386])).

tff(c_389,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_8,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_2,B_3] : m1_subset_1(k6_subset_1(A_2,B_3),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_57,A_58,B_59] :
      ( ~ v1_xboole_0(A_57)
      | ~ r2_hidden(A_58,k6_subset_1(A_57,B_59)) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_83,plain,(
    ! [A_57,B_59] :
      ( ~ v1_xboole_0(A_57)
      | k6_subset_1(A_57,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_393,plain,(
    ! [B_59] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_389,c_83])).

tff(c_28,plain,(
    ! [B_37,A_36] :
      ( k6_subset_1(B_37,A_36) != k1_xboole_0
      | B_37 = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_215,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_209,c_28])).

tff(c_221,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_215])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_221])).

tff(c_409,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_408,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_449,plain,(
    ! [B_167,A_168] :
      ( v2_tex_2(B_167,A_168)
      | ~ v3_tex_2(B_167,A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_456,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_449])).

tff(c_460,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_408,c_456])).

tff(c_508,plain,(
    ! [B_183,A_184] :
      ( v1_zfmisc_1(B_183)
      | ~ v2_tex_2(B_183,A_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | v1_xboole_0(B_183)
      | ~ l1_pre_topc(A_184)
      | ~ v2_tdlat_3(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_515,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_508])).

tff(c_519,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_460,c_515])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_409,c_519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:22:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.40  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_mcart_1 > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.75/1.40  
% 2.75/1.40  %Foreground sorts:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Background operators:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Foreground operators:
% 2.75/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.40  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.75/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.75/1.40  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.75/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.40  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.75/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.75/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.40  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.75/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.40  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.75/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.40  
% 2.75/1.42  tff(f_138, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.75/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.75/1.42  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.75/1.42  tff(f_118, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.75/1.42  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.75/1.42  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.75/1.42  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.75/1.42  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.75/1.42  tff(f_86, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 2.75/1.42  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_38, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_54, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_56, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 2.75/1.42  tff(c_48, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_58, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 2.75/1.42  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.42  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_107, plain, (![A_82, B_83]: ('#skF_2'(A_82, B_83)!=B_83 | v3_tex_2(B_83, A_82) | ~v2_tex_2(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.42  tff(c_114, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_107])).
% 2.75/1.42  tff(c_118, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_114])).
% 2.75/1.42  tff(c_119, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_118])).
% 2.75/1.42  tff(c_120, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_119])).
% 2.75/1.42  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_42, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.75/1.42  tff(c_179, plain, (![B_94, A_95]: (v2_tex_2(B_94, A_95) | ~v1_zfmisc_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(B_94) | ~l1_pre_topc(A_95) | ~v2_tdlat_3(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.75/1.42  tff(c_189, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_179])).
% 2.75/1.42  tff(c_194, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_56, c_189])).
% 2.75/1.42  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_120, c_194])).
% 2.75/1.42  tff(c_197, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_119])).
% 2.75/1.42  tff(c_198, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_119])).
% 2.75/1.42  tff(c_199, plain, (![B_96, A_97]: (r1_tarski(B_96, '#skF_2'(A_97, B_96)) | v3_tex_2(B_96, A_97) | ~v2_tex_2(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.42  tff(c_204, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_199])).
% 2.75/1.42  tff(c_208, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_198, c_204])).
% 2.75/1.42  tff(c_209, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_208])).
% 2.75/1.42  tff(c_30, plain, (![B_40, A_38]: (B_40=A_38 | ~r1_tarski(A_38, B_40) | ~v1_zfmisc_1(B_40) | v1_xboole_0(B_40) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.42  tff(c_212, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_209, c_30])).
% 2.75/1.42  tff(c_218, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_197, c_212])).
% 2.75/1.42  tff(c_222, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_218])).
% 2.75/1.42  tff(c_226, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_222])).
% 2.75/1.42  tff(c_228, plain, (![A_100, B_101]: (v2_tex_2('#skF_2'(A_100, B_101), A_100) | v3_tex_2(B_101, A_100) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.42  tff(c_233, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_228])).
% 2.75/1.42  tff(c_237, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_198, c_233])).
% 2.75/1.42  tff(c_238, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_237])).
% 2.75/1.42  tff(c_265, plain, (![A_106, B_107]: (m1_subset_1('#skF_2'(A_106, B_107), k1_zfmisc_1(u1_struct_0(A_106))) | v3_tex_2(B_107, A_106) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.42  tff(c_34, plain, (![B_43, A_41]: (v1_zfmisc_1(B_43) | ~v2_tex_2(B_43, A_41) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_41))) | v1_xboole_0(B_43) | ~l1_pre_topc(A_41) | ~v2_tdlat_3(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.75/1.42  tff(c_373, plain, (![A_133, B_134]: (v1_zfmisc_1('#skF_2'(A_133, B_134)) | ~v2_tex_2('#skF_2'(A_133, B_134), A_133) | v1_xboole_0('#skF_2'(A_133, B_134)) | ~v2_tdlat_3(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133) | v3_tex_2(B_134, A_133) | ~v2_tex_2(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_265, c_34])).
% 2.75/1.42  tff(c_379, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_238, c_373])).
% 2.75/1.42  tff(c_386, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_198, c_44, c_42, c_379])).
% 2.75/1.42  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_226, c_222, c_386])).
% 2.75/1.42  tff(c_389, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_218])).
% 2.75/1.42  tff(c_8, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.42  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k6_subset_1(A_2, B_3), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.42  tff(c_69, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.75/1.42  tff(c_78, plain, (![A_57, A_58, B_59]: (~v1_xboole_0(A_57) | ~r2_hidden(A_58, k6_subset_1(A_57, B_59)))), inference(resolution, [status(thm)], [c_4, c_69])).
% 2.75/1.42  tff(c_83, plain, (![A_57, B_59]: (~v1_xboole_0(A_57) | k6_subset_1(A_57, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_78])).
% 2.75/1.42  tff(c_393, plain, (![B_59]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_389, c_83])).
% 2.75/1.42  tff(c_28, plain, (![B_37, A_36]: (k6_subset_1(B_37, A_36)!=k1_xboole_0 | B_37=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.75/1.42  tff(c_215, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_209, c_28])).
% 2.75/1.42  tff(c_221, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_197, c_215])).
% 2.75/1.42  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_393, c_221])).
% 2.75/1.42  tff(c_409, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.75/1.42  tff(c_408, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 2.75/1.42  tff(c_449, plain, (![B_167, A_168]: (v2_tex_2(B_167, A_168) | ~v3_tex_2(B_167, A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.42  tff(c_456, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_449])).
% 2.75/1.42  tff(c_460, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_408, c_456])).
% 2.75/1.42  tff(c_508, plain, (![B_183, A_184]: (v1_zfmisc_1(B_183) | ~v2_tex_2(B_183, A_184) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_184))) | v1_xboole_0(B_183) | ~l1_pre_topc(A_184) | ~v2_tdlat_3(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.75/1.42  tff(c_515, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_508])).
% 2.75/1.42  tff(c_519, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_460, c_515])).
% 2.75/1.42  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_409, c_519])).
% 2.75/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.42  
% 2.75/1.42  Inference rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Ref     : 0
% 2.75/1.42  #Sup     : 83
% 2.75/1.42  #Fact    : 0
% 2.75/1.42  #Define  : 0
% 2.75/1.42  #Split   : 6
% 2.75/1.42  #Chain   : 0
% 2.75/1.42  #Close   : 0
% 2.75/1.42  
% 2.75/1.42  Ordering : KBO
% 2.75/1.42  
% 2.75/1.42  Simplification rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Subsume      : 13
% 2.75/1.42  #Demod        : 68
% 2.75/1.42  #Tautology    : 12
% 2.75/1.42  #SimpNegUnit  : 19
% 2.75/1.42  #BackRed      : 1
% 2.75/1.42  
% 2.75/1.42  #Partial instantiations: 0
% 2.75/1.42  #Strategies tried      : 1
% 2.75/1.42  
% 2.75/1.42  Timing (in seconds)
% 2.75/1.42  ----------------------
% 2.75/1.42  Preprocessing        : 0.30
% 2.75/1.42  Parsing              : 0.17
% 2.75/1.42  CNF conversion       : 0.02
% 2.75/1.42  Main loop            : 0.31
% 2.75/1.42  Inferencing          : 0.12
% 2.75/1.42  Reduction            : 0.09
% 2.75/1.42  Demodulation         : 0.06
% 2.75/1.42  BG Simplification    : 0.02
% 2.75/1.42  Subsumption          : 0.06
% 2.75/1.42  Abstraction          : 0.01
% 2.75/1.42  MUC search           : 0.00
% 2.75/1.42  Cooper               : 0.00
% 2.75/1.42  Total                : 0.65
% 2.75/1.42  Index Insertion      : 0.00
% 2.75/1.42  Index Deletion       : 0.00
% 2.75/1.42  Index Matching       : 0.00
% 2.75/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
