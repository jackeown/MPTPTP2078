%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:16 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 386 expanded)
%              Number of leaves         :   31 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :  212 (1452 expanded)
%              Number of equality atoms :   20 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_70,axiom,(
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

tff(f_110,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44])).

tff(c_4,plain,(
    ! [A_3] :
      ( v1_zfmisc_1(A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_94,plain,(
    ! [A_50,B_51] :
      ( '#skF_2'(A_50,B_51) != B_51
      | v3_tex_2(B_51,A_50)
      | ~ v2_tex_2(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_105,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101])).

tff(c_106,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_105])).

tff(c_107,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_148,plain,(
    ! [B_58,A_59] :
      ( v2_tex_2(B_58,A_59)
      | ~ v1_zfmisc_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | v1_xboole_0(B_58)
      | ~ l1_pre_topc(A_59)
      | ~ v2_tdlat_3(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_158,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_148])).

tff(c_163,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_52,c_158])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_107,c_163])).

tff(c_166,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_167,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_179,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,'#skF_2'(A_63,B_62))
      | v3_tex_2(B_62,A_63)
      | ~ v2_tex_2(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_184,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_188,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_167,c_184])).

tff(c_189,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_188])).

tff(c_26,plain,(
    ! [B_24,A_22] :
      ( B_24 = A_22
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_192,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_26])).

tff(c_198,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_166,c_192])).

tff(c_215,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_219,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_168,plain,(
    ! [A_60,B_61] :
      ( v2_tex_2('#skF_2'(A_60,B_61),A_60)
      | v3_tex_2(B_61,A_60)
      | ~ v2_tex_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_173,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_168])).

tff(c_177,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_167,c_173])).

tff(c_178,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_177])).

tff(c_18,plain,(
    ! [A_10,B_16] :
      ( m1_subset_1('#skF_2'(A_10,B_16),k1_zfmisc_1(u1_struct_0(A_10)))
      | v3_tex_2(B_16,A_10)
      | ~ v2_tex_2(B_16,A_10)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_242,plain,(
    ! [B_68,A_69] :
      ( v1_zfmisc_1(B_68)
      | ~ v2_tex_2(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | v1_xboole_0(B_68)
      | ~ l1_pre_topc(A_69)
      | ~ v2_tdlat_3(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_353,plain,(
    ! [A_97,B_98] :
      ( v1_zfmisc_1('#skF_2'(A_97,B_98))
      | ~ v2_tex_2('#skF_2'(A_97,B_98),A_97)
      | v1_xboole_0('#skF_2'(A_97,B_98))
      | ~ v2_tdlat_3(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97)
      | v3_tex_2(B_98,A_97)
      | ~ v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_18,c_242])).

tff(c_359,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_353])).

tff(c_366,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_167,c_40,c_38,c_359])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42,c_219,c_215,c_366])).

tff(c_369,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_4,B_5] : m1_subset_1(k6_subset_1(A_4,B_5),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,(
    ! [A_39,A_40,B_41] :
      ( ~ v1_xboole_0(A_39)
      | ~ r2_hidden(A_40,k6_subset_1(A_39,B_41)) ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_78,plain,(
    ! [A_39,B_41] :
      ( ~ v1_xboole_0(A_39)
      | k6_subset_1(A_39,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_373,plain,(
    ! [B_41] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_369,c_78])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( k6_subset_1(B_21,A_20) != k1_xboole_0
      | B_21 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_195,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_189,c_24])).

tff(c_201,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_195])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_201])).

tff(c_378,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_377,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_411,plain,(
    ! [B_115,A_116] :
      ( v2_tex_2(B_115,A_116)
      | ~ v3_tex_2(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_418,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_411])).

tff(c_422,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_377,c_418])).

tff(c_491,plain,(
    ! [B_129,A_130] :
      ( v1_zfmisc_1(B_129)
      | ~ v2_tex_2(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | v1_xboole_0(B_129)
      | ~ l1_pre_topc(A_130)
      | ~ v2_tdlat_3(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_501,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_491])).

tff(c_506,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_422,c_501])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_378,c_506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.39  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.81/1.39  
% 2.81/1.39  %Foreground sorts:
% 2.81/1.39  
% 2.81/1.39  
% 2.81/1.39  %Background operators:
% 2.81/1.39  
% 2.81/1.39  
% 2.81/1.39  %Foreground operators:
% 2.81/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.81/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.81/1.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.81/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.81/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.39  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.81/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.39  
% 2.81/1.40  tff(f_130, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.81/1.40  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.81/1.40  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.81/1.40  tff(f_110, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.81/1.40  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.81/1.40  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.81/1.40  tff(f_39, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.81/1.40  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.81/1.40  tff(f_78, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 2.81/1.40  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_34, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_50, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_52, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.81/1.40  tff(c_44, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_54, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44])).
% 2.81/1.40  tff(c_4, plain, (![A_3]: (v1_zfmisc_1(A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.40  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_94, plain, (![A_50, B_51]: ('#skF_2'(A_50, B_51)!=B_51 | v3_tex_2(B_51, A_50) | ~v2_tex_2(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.40  tff(c_101, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_94])).
% 2.81/1.40  tff(c_105, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_101])).
% 2.81/1.40  tff(c_106, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_105])).
% 2.81/1.40  tff(c_107, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_106])).
% 2.81/1.40  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_38, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.81/1.40  tff(c_148, plain, (![B_58, A_59]: (v2_tex_2(B_58, A_59) | ~v1_zfmisc_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | v1_xboole_0(B_58) | ~l1_pre_topc(A_59) | ~v2_tdlat_3(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.81/1.40  tff(c_158, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_148])).
% 2.81/1.40  tff(c_163, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_52, c_158])).
% 2.81/1.40  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_107, c_163])).
% 2.81/1.40  tff(c_166, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_106])).
% 2.81/1.40  tff(c_167, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_106])).
% 2.81/1.40  tff(c_179, plain, (![B_62, A_63]: (r1_tarski(B_62, '#skF_2'(A_63, B_62)) | v3_tex_2(B_62, A_63) | ~v2_tex_2(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.40  tff(c_184, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_179])).
% 2.81/1.40  tff(c_188, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_167, c_184])).
% 2.81/1.40  tff(c_189, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_188])).
% 2.81/1.40  tff(c_26, plain, (![B_24, A_22]: (B_24=A_22 | ~r1_tarski(A_22, B_24) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.81/1.40  tff(c_192, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_189, c_26])).
% 2.81/1.40  tff(c_198, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_166, c_192])).
% 2.81/1.40  tff(c_215, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_198])).
% 2.81/1.40  tff(c_219, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_215])).
% 2.81/1.40  tff(c_168, plain, (![A_60, B_61]: (v2_tex_2('#skF_2'(A_60, B_61), A_60) | v3_tex_2(B_61, A_60) | ~v2_tex_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.40  tff(c_173, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_168])).
% 2.81/1.40  tff(c_177, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_167, c_173])).
% 2.81/1.40  tff(c_178, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_177])).
% 2.81/1.40  tff(c_18, plain, (![A_10, B_16]: (m1_subset_1('#skF_2'(A_10, B_16), k1_zfmisc_1(u1_struct_0(A_10))) | v3_tex_2(B_16, A_10) | ~v2_tex_2(B_16, A_10) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.40  tff(c_242, plain, (![B_68, A_69]: (v1_zfmisc_1(B_68) | ~v2_tex_2(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | v1_xboole_0(B_68) | ~l1_pre_topc(A_69) | ~v2_tdlat_3(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.81/1.40  tff(c_353, plain, (![A_97, B_98]: (v1_zfmisc_1('#skF_2'(A_97, B_98)) | ~v2_tex_2('#skF_2'(A_97, B_98), A_97) | v1_xboole_0('#skF_2'(A_97, B_98)) | ~v2_tdlat_3(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97) | v3_tex_2(B_98, A_97) | ~v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_18, c_242])).
% 2.81/1.40  tff(c_359, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_178, c_353])).
% 2.81/1.40  tff(c_366, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_167, c_40, c_38, c_359])).
% 2.81/1.40  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_42, c_219, c_215, c_366])).
% 2.81/1.40  tff(c_369, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_198])).
% 2.81/1.40  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.40  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(k6_subset_1(A_4, B_5), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.40  tff(c_64, plain, (![C_34, B_35, A_36]: (~v1_xboole_0(C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.40  tff(c_73, plain, (![A_39, A_40, B_41]: (~v1_xboole_0(A_39) | ~r2_hidden(A_40, k6_subset_1(A_39, B_41)))), inference(resolution, [status(thm)], [c_6, c_64])).
% 2.81/1.40  tff(c_78, plain, (![A_39, B_41]: (~v1_xboole_0(A_39) | k6_subset_1(A_39, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_73])).
% 2.81/1.40  tff(c_373, plain, (![B_41]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_369, c_78])).
% 2.81/1.40  tff(c_24, plain, (![B_21, A_20]: (k6_subset_1(B_21, A_20)!=k1_xboole_0 | B_21=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.81/1.40  tff(c_195, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_189, c_24])).
% 2.81/1.40  tff(c_201, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_166, c_195])).
% 2.81/1.40  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_201])).
% 2.81/1.40  tff(c_378, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.81/1.40  tff(c_377, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 2.81/1.40  tff(c_411, plain, (![B_115, A_116]: (v2_tex_2(B_115, A_116) | ~v3_tex_2(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.40  tff(c_418, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_411])).
% 2.81/1.40  tff(c_422, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_377, c_418])).
% 2.81/1.40  tff(c_491, plain, (![B_129, A_130]: (v1_zfmisc_1(B_129) | ~v2_tex_2(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | v1_xboole_0(B_129) | ~l1_pre_topc(A_130) | ~v2_tdlat_3(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.81/1.40  tff(c_501, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_491])).
% 2.81/1.40  tff(c_506, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_422, c_501])).
% 2.81/1.40  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_378, c_506])).
% 2.81/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  Inference rules
% 2.81/1.40  ----------------------
% 2.81/1.40  #Ref     : 0
% 2.81/1.40  #Sup     : 84
% 2.81/1.40  #Fact    : 0
% 2.81/1.40  #Define  : 0
% 2.81/1.40  #Split   : 6
% 2.81/1.40  #Chain   : 0
% 2.81/1.40  #Close   : 0
% 2.81/1.40  
% 2.81/1.40  Ordering : KBO
% 2.81/1.40  
% 2.81/1.40  Simplification rules
% 2.81/1.40  ----------------------
% 2.81/1.40  #Subsume      : 14
% 2.81/1.40  #Demod        : 63
% 2.81/1.40  #Tautology    : 12
% 2.81/1.40  #SimpNegUnit  : 17
% 2.81/1.40  #BackRed      : 1
% 2.81/1.40  
% 2.81/1.40  #Partial instantiations: 0
% 2.81/1.40  #Strategies tried      : 1
% 2.81/1.40  
% 2.81/1.40  Timing (in seconds)
% 2.81/1.40  ----------------------
% 2.81/1.41  Preprocessing        : 0.29
% 2.81/1.41  Parsing              : 0.16
% 2.81/1.41  CNF conversion       : 0.02
% 2.81/1.41  Main loop            : 0.31
% 2.81/1.41  Inferencing          : 0.12
% 2.81/1.41  Reduction            : 0.08
% 2.81/1.41  Demodulation         : 0.06
% 2.81/1.41  BG Simplification    : 0.02
% 2.81/1.41  Subsumption          : 0.07
% 2.81/1.41  Abstraction          : 0.01
% 2.81/1.41  MUC search           : 0.00
% 2.81/1.41  Cooper               : 0.00
% 2.81/1.41  Total                : 0.64
% 2.81/1.41  Index Insertion      : 0.00
% 2.81/1.41  Index Deletion       : 0.00
% 2.81/1.41  Index Matching       : 0.00
% 2.81/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
