%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:15 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 977 expanded)
%              Number of leaves         :   35 ( 337 expanded)
%              Depth                    :   13
%              Number of atoms          :  445 (3237 expanded)
%              Number of equality atoms :   44 ( 313 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_83,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_115,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_58,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_61,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_63,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_52])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_373,plain,(
    ! [A_106,B_107] :
      ( '#skF_1'(A_106,B_107) != B_107
      | v3_tex_2(B_107,A_106)
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_376,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_373])).

tff(c_379,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_376])).

tff(c_380,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_379])).

tff(c_383,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_219,plain,(
    ! [A_77,B_78] :
      ( '#skF_1'(A_77,B_78) != B_78
      | v3_tex_2(B_78,A_77)
      | ~ v2_tex_2(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_222,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_219])).

tff(c_225,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_222])).

tff(c_226,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_225])).

tff(c_227,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_73,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(k2_xboole_0(B_7,A_6))
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [A_40,B_41] :
      ( ~ v1_xboole_0(A_40)
      | v1_xboole_0(k3_xboole_0(A_40,B_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_89,plain,(
    ! [A_44,B_45] :
      ( ~ v1_xboole_0(A_44)
      | v1_xboole_0(k3_xboole_0(A_44,B_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_130,plain,(
    ! [A_58,B_59,B_60] :
      ( k3_xboole_0(k3_xboole_0(A_58,B_59),B_60) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_79,c_94])).

tff(c_85,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(A_42,B_43)
      | k3_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_xboole_0(B_5,A_4)
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [B_52,A_53] :
      ( r1_xboole_0(B_52,A_53)
      | k3_xboole_0(A_53,B_52) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [B_52,A_53] :
      ( k3_xboole_0(B_52,A_53) = k1_xboole_0
      | k3_xboole_0(A_53,B_52) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_154,plain,(
    ! [B_61,A_62,B_63] :
      ( k3_xboole_0(B_61,k3_xboole_0(A_62,B_63)) = k1_xboole_0
      | ~ v1_xboole_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_118])).

tff(c_171,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_79])).

tff(c_193,plain,(
    ! [A_62] : ~ v1_xboole_0(A_62) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_36,plain,(
    ! [B_31,A_29] :
      ( v2_tex_2(B_31,A_29)
      | ~ v1_zfmisc_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_29)
      | ~ v2_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_245,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ v1_zfmisc_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_36])).

tff(c_248,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_245])).

tff(c_251,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_61,c_248])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_227,c_251])).

tff(c_254,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_255,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_265,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,'#skF_1'(A_88,B_87))
      | v3_tex_2(B_87,A_88)
      | ~ v2_tex_2(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_267,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_265])).

tff(c_270,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_255,c_267])).

tff(c_271,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_270])).

tff(c_34,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_194,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_193,c_34])).

tff(c_280,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_271,c_194])).

tff(c_285,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_280])).

tff(c_256,plain,(
    ! [A_85,B_86] :
      ( v2_tex_2('#skF_1'(A_85,B_86),A_85)
      | v3_tex_2(B_86,A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_258,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_256])).

tff(c_261,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_255,c_258])).

tff(c_262,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_261])).

tff(c_28,plain,(
    ! [A_16,B_22] :
      ( m1_subset_1('#skF_1'(A_16,B_22),k1_zfmisc_1(u1_struct_0(A_16)))
      | v3_tex_2(B_22,A_16)
      | ~ v2_tex_2(B_22,A_16)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [B_31,A_29] :
      ( v1_zfmisc_1(B_31)
      | ~ v2_tex_2(B_31,A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_29)
      | ~ v2_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_302,plain,(
    ! [B_91,A_92] :
      ( v1_zfmisc_1(B_91)
      | ~ v2_tex_2(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_tdlat_3(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_38])).

tff(c_342,plain,(
    ! [A_99,B_100] :
      ( v1_zfmisc_1('#skF_1'(A_99,B_100))
      | ~ v2_tex_2('#skF_1'(A_99,B_100),A_99)
      | ~ v2_tdlat_3(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99)
      | v3_tex_2(B_100,A_99)
      | ~ v2_tex_2(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_28,c_302])).

tff(c_344,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_262,c_342])).

tff(c_347,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_255,c_48,c_46,c_344])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50,c_285,c_347])).

tff(c_350,plain,(
    ! [B_61] :
      ( ~ v1_xboole_0(B_61)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_351,plain,(
    ! [B_61] : ~ v1_xboole_0(B_61) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_431,plain,(
    ! [B_122,A_123] :
      ( v2_tex_2(B_122,A_123)
      | ~ v1_zfmisc_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_tdlat_3(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_36])).

tff(c_437,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_431])).

tff(c_441,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_61,c_437])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_383,c_441])).

tff(c_444,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_445,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_455,plain,(
    ! [B_128,A_129] :
      ( r1_tarski(B_128,'#skF_1'(A_129,B_128))
      | v3_tex_2(B_128,A_129)
      | ~ v2_tex_2(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_457,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_455])).

tff(c_460,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_445,c_457])).

tff(c_461,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_460])).

tff(c_359,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_351,c_34])).

tff(c_470,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_461,c_359])).

tff(c_475,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_470])).

tff(c_448,plain,(
    ! [A_126,B_127] :
      ( v2_tex_2('#skF_1'(A_126,B_127),A_126)
      | v3_tex_2(B_127,A_126)
      | ~ v2_tex_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_450,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_448])).

tff(c_453,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_445,c_450])).

tff(c_454,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_453])).

tff(c_494,plain,(
    ! [B_132,A_133] :
      ( v1_zfmisc_1(B_132)
      | ~ v2_tex_2(B_132,A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ v2_tdlat_3(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_38])).

tff(c_534,plain,(
    ! [A_140,B_141] :
      ( v1_zfmisc_1('#skF_1'(A_140,B_141))
      | ~ v2_tex_2('#skF_1'(A_140,B_141),A_140)
      | ~ v2_tdlat_3(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140)
      | v3_tex_2(B_141,A_140)
      | ~ v2_tex_2(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_28,c_494])).

tff(c_536,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_454,c_534])).

tff(c_539,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_445,c_48,c_46,c_536])).

tff(c_541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50,c_475,c_539])).

tff(c_542,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_93,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_548,plain,(
    ! [B_45] : k3_xboole_0(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_542,c_93])).

tff(c_16,plain,(
    ! [A_12] :
      ( v1_zfmisc_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_662,plain,(
    ! [A_147,B_148] :
      ( '#skF_1'(A_147,B_148) != B_148
      | v3_tex_2(B_148,A_147)
      | ~ v2_tex_2(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_665,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_662])).

tff(c_668,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_665])).

tff(c_669,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_668])).

tff(c_670,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_694,plain,(
    ! [B_157,A_158] :
      ( v2_tex_2(B_157,A_158)
      | ~ v1_zfmisc_1(B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | v1_xboole_0(B_157)
      | ~ l1_pre_topc(A_158)
      | ~ v2_tdlat_3(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_697,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_694])).

tff(c_700,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_61,c_697])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_670,c_700])).

tff(c_703,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_704,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_717,plain,(
    ! [B_165,A_166] :
      ( r1_tarski(B_165,'#skF_1'(A_166,B_165))
      | v3_tex_2(B_165,A_166)
      | ~ v2_tex_2(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_719,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_717])).

tff(c_722,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_704,c_719])).

tff(c_723,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_722])).

tff(c_732,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_723,c_34])).

tff(c_741,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_703,c_732])).

tff(c_742,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_746,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_742])).

tff(c_708,plain,(
    ! [A_159,B_160] :
      ( v2_tex_2('#skF_1'(A_159,B_160),A_159)
      | v3_tex_2(B_160,A_159)
      | ~ v2_tex_2(B_160,A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_710,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_708])).

tff(c_713,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_704,c_710])).

tff(c_714,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_713])).

tff(c_764,plain,(
    ! [B_169,A_170] :
      ( v1_zfmisc_1(B_169)
      | ~ v2_tex_2(B_169,A_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | v1_xboole_0(B_169)
      | ~ l1_pre_topc(A_170)
      | ~ v2_tdlat_3(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_817,plain,(
    ! [A_181,B_182] :
      ( v1_zfmisc_1('#skF_1'(A_181,B_182))
      | ~ v2_tex_2('#skF_1'(A_181,B_182),A_181)
      | v1_xboole_0('#skF_1'(A_181,B_182))
      | ~ v2_tdlat_3(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181)
      | v3_tex_2(B_182,A_181)
      | ~ v2_tex_2(B_182,A_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(resolution,[status(thm)],[c_28,c_764])).

tff(c_821,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_714,c_817])).

tff(c_825,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_704,c_48,c_46,c_821])).

tff(c_827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50,c_746,c_742,c_825])).

tff(c_828,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_836,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_828,c_6])).

tff(c_88,plain,(
    ! [B_43,A_42] :
      ( r1_xboole_0(B_43,A_42)
      | k3_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_120,plain,(
    ! [B_54,A_55] :
      ( ~ r1_xboole_0(B_54,A_55)
      | ~ r1_tarski(B_54,A_55)
      | v1_xboole_0(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_127,plain,(
    ! [B_43,A_42] :
      ( ~ r1_tarski(B_43,A_42)
      | v1_xboole_0(B_43)
      | k3_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_88,c_120])).

tff(c_726,plain,
    ( v1_xboole_0('#skF_3')
    | k3_xboole_0('#skF_1'('#skF_2','#skF_3'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_723,c_127])).

tff(c_735,plain,(
    k3_xboole_0('#skF_1'('#skF_2','#skF_3'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_726])).

tff(c_839,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_735])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_839])).

tff(c_849,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_848,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1251,plain,(
    ! [B_262,A_263] :
      ( v2_tex_2(B_262,A_263)
      | ~ v3_tex_2(B_262,A_263)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1254,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1251])).

tff(c_1257,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_848,c_1254])).

tff(c_1320,plain,(
    ! [B_277,A_278] :
      ( v1_zfmisc_1(B_277)
      | ~ v2_tex_2(B_277,A_278)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_278)))
      | v1_xboole_0(B_277)
      | ~ l1_pre_topc(A_278)
      | ~ v2_tdlat_3(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1323,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1320])).

tff(c_1326,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1257,c_1323])).

tff(c_1328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_849,c_1326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.61  
% 3.58/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.62  %$ v3_tex_2 > v2_tex_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.58/1.62  
% 3.58/1.62  %Foreground sorts:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Background operators:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Foreground operators:
% 3.58/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.58/1.62  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.58/1.62  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.58/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.58/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.62  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.58/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.58/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.58/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.62  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.58/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.62  
% 3.95/1.66  tff(f_135, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.95/1.66  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.95/1.66  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.95/1.66  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 3.95/1.66  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.95/1.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.95/1.66  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.95/1.66  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.95/1.66  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.95/1.66  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.95/1.66  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.95/1.66  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_58, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_61, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 3.95/1.66  tff(c_52, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_63, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_52])).
% 3.95/1.66  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_373, plain, (![A_106, B_107]: ('#skF_1'(A_106, B_107)!=B_107 | v3_tex_2(B_107, A_106) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_376, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_373])).
% 3.95/1.66  tff(c_379, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_376])).
% 3.95/1.66  tff(c_380, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_379])).
% 3.95/1.66  tff(c_383, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_380])).
% 3.95/1.66  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_46, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.95/1.66  tff(c_219, plain, (![A_77, B_78]: ('#skF_1'(A_77, B_78)!=B_78 | v3_tex_2(B_78, A_77) | ~v2_tex_2(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_222, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_219])).
% 3.95/1.66  tff(c_225, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_222])).
% 3.95/1.66  tff(c_226, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_225])).
% 3.95/1.66  tff(c_227, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_226])).
% 3.95/1.66  tff(c_73, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k3_xboole_0(A_40, B_41))=A_40)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.66  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(k2_xboole_0(B_7, A_6)) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.66  tff(c_79, plain, (![A_40, B_41]: (~v1_xboole_0(A_40) | v1_xboole_0(k3_xboole_0(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_10])).
% 3.95/1.66  tff(c_89, plain, (![A_44, B_45]: (~v1_xboole_0(A_44) | v1_xboole_0(k3_xboole_0(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_10])).
% 3.95/1.66  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.95/1.66  tff(c_94, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_89, c_6])).
% 3.95/1.66  tff(c_130, plain, (![A_58, B_59, B_60]: (k3_xboole_0(k3_xboole_0(A_58, B_59), B_60)=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_79, c_94])).
% 3.95/1.66  tff(c_85, plain, (![A_42, B_43]: (r1_xboole_0(A_42, B_43) | k3_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.95/1.66  tff(c_8, plain, (![B_5, A_4]: (r1_xboole_0(B_5, A_4) | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.95/1.66  tff(c_112, plain, (![B_52, A_53]: (r1_xboole_0(B_52, A_53) | k3_xboole_0(A_53, B_52)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_8])).
% 3.95/1.66  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.95/1.66  tff(c_118, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k1_xboole_0 | k3_xboole_0(A_53, B_52)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_112, c_2])).
% 3.95/1.66  tff(c_154, plain, (![B_61, A_62, B_63]: (k3_xboole_0(B_61, k3_xboole_0(A_62, B_63))=k1_xboole_0 | ~v1_xboole_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_130, c_118])).
% 3.95/1.66  tff(c_171, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_154, c_79])).
% 3.95/1.66  tff(c_193, plain, (![A_62]: (~v1_xboole_0(A_62))), inference(splitLeft, [status(thm)], [c_171])).
% 3.95/1.66  tff(c_36, plain, (![B_31, A_29]: (v2_tex_2(B_31, A_29) | ~v1_zfmisc_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | v1_xboole_0(B_31) | ~l1_pre_topc(A_29) | ~v2_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.95/1.66  tff(c_245, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~v1_zfmisc_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(negUnitSimplification, [status(thm)], [c_193, c_36])).
% 3.95/1.66  tff(c_248, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_245])).
% 3.95/1.66  tff(c_251, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_61, c_248])).
% 3.95/1.66  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_227, c_251])).
% 3.95/1.66  tff(c_254, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_226])).
% 3.95/1.66  tff(c_255, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_226])).
% 3.95/1.66  tff(c_265, plain, (![B_87, A_88]: (r1_tarski(B_87, '#skF_1'(A_88, B_87)) | v3_tex_2(B_87, A_88) | ~v2_tex_2(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_267, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_265])).
% 3.95/1.66  tff(c_270, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_255, c_267])).
% 3.95/1.66  tff(c_271, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_270])).
% 3.95/1.66  tff(c_34, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.95/1.66  tff(c_194, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28))), inference(negUnitSimplification, [status(thm)], [c_193, c_193, c_34])).
% 3.95/1.66  tff(c_280, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_271, c_194])).
% 3.95/1.66  tff(c_285, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_254, c_280])).
% 3.95/1.66  tff(c_256, plain, (![A_85, B_86]: (v2_tex_2('#skF_1'(A_85, B_86), A_85) | v3_tex_2(B_86, A_85) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_258, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_256])).
% 3.95/1.66  tff(c_261, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_255, c_258])).
% 3.95/1.66  tff(c_262, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_261])).
% 3.95/1.66  tff(c_28, plain, (![A_16, B_22]: (m1_subset_1('#skF_1'(A_16, B_22), k1_zfmisc_1(u1_struct_0(A_16))) | v3_tex_2(B_22, A_16) | ~v2_tex_2(B_22, A_16) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_38, plain, (![B_31, A_29]: (v1_zfmisc_1(B_31) | ~v2_tex_2(B_31, A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | v1_xboole_0(B_31) | ~l1_pre_topc(A_29) | ~v2_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.95/1.66  tff(c_302, plain, (![B_91, A_92]: (v1_zfmisc_1(B_91) | ~v2_tex_2(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_tdlat_3(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(negUnitSimplification, [status(thm)], [c_193, c_38])).
% 3.95/1.66  tff(c_342, plain, (![A_99, B_100]: (v1_zfmisc_1('#skF_1'(A_99, B_100)) | ~v2_tex_2('#skF_1'(A_99, B_100), A_99) | ~v2_tdlat_3(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99) | v3_tex_2(B_100, A_99) | ~v2_tex_2(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_28, c_302])).
% 3.95/1.66  tff(c_344, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_262, c_342])).
% 3.95/1.66  tff(c_347, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_255, c_48, c_46, c_344])).
% 3.95/1.66  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_50, c_285, c_347])).
% 3.95/1.66  tff(c_350, plain, (![B_61]: (~v1_xboole_0(B_61) | v1_xboole_0(k1_xboole_0))), inference(splitRight, [status(thm)], [c_171])).
% 3.95/1.66  tff(c_351, plain, (![B_61]: (~v1_xboole_0(B_61))), inference(splitLeft, [status(thm)], [c_350])).
% 3.95/1.66  tff(c_431, plain, (![B_122, A_123]: (v2_tex_2(B_122, A_123) | ~v1_zfmisc_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_tdlat_3(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(negUnitSimplification, [status(thm)], [c_351, c_36])).
% 3.95/1.66  tff(c_437, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_431])).
% 3.95/1.66  tff(c_441, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_61, c_437])).
% 3.95/1.66  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_383, c_441])).
% 3.95/1.66  tff(c_444, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_380])).
% 3.95/1.66  tff(c_445, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_380])).
% 3.95/1.66  tff(c_455, plain, (![B_128, A_129]: (r1_tarski(B_128, '#skF_1'(A_129, B_128)) | v3_tex_2(B_128, A_129) | ~v2_tex_2(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_457, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_455])).
% 3.95/1.66  tff(c_460, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_445, c_457])).
% 3.95/1.66  tff(c_461, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_460])).
% 3.95/1.66  tff(c_359, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28))), inference(negUnitSimplification, [status(thm)], [c_351, c_351, c_34])).
% 3.95/1.66  tff(c_470, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_461, c_359])).
% 3.95/1.66  tff(c_475, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_444, c_470])).
% 3.95/1.66  tff(c_448, plain, (![A_126, B_127]: (v2_tex_2('#skF_1'(A_126, B_127), A_126) | v3_tex_2(B_127, A_126) | ~v2_tex_2(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_450, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_448])).
% 3.95/1.66  tff(c_453, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_445, c_450])).
% 3.95/1.66  tff(c_454, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_453])).
% 3.95/1.66  tff(c_494, plain, (![B_132, A_133]: (v1_zfmisc_1(B_132) | ~v2_tex_2(B_132, A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~v2_tdlat_3(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(negUnitSimplification, [status(thm)], [c_351, c_38])).
% 3.95/1.66  tff(c_534, plain, (![A_140, B_141]: (v1_zfmisc_1('#skF_1'(A_140, B_141)) | ~v2_tex_2('#skF_1'(A_140, B_141), A_140) | ~v2_tdlat_3(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140) | v3_tex_2(B_141, A_140) | ~v2_tex_2(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_28, c_494])).
% 3.95/1.66  tff(c_536, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_454, c_534])).
% 3.95/1.66  tff(c_539, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_445, c_48, c_46, c_536])).
% 3.95/1.66  tff(c_541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_50, c_475, c_539])).
% 3.95/1.66  tff(c_542, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_350])).
% 3.95/1.66  tff(c_93, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_89, c_6])).
% 3.95/1.66  tff(c_548, plain, (![B_45]: (k3_xboole_0(k1_xboole_0, B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_542, c_93])).
% 3.95/1.66  tff(c_16, plain, (![A_12]: (v1_zfmisc_1(A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.95/1.66  tff(c_662, plain, (![A_147, B_148]: ('#skF_1'(A_147, B_148)!=B_148 | v3_tex_2(B_148, A_147) | ~v2_tex_2(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_665, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_662])).
% 3.95/1.66  tff(c_668, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_665])).
% 3.95/1.66  tff(c_669, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_668])).
% 3.95/1.66  tff(c_670, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_669])).
% 3.95/1.66  tff(c_694, plain, (![B_157, A_158]: (v2_tex_2(B_157, A_158) | ~v1_zfmisc_1(B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | v1_xboole_0(B_157) | ~l1_pre_topc(A_158) | ~v2_tdlat_3(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.95/1.66  tff(c_697, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_694])).
% 3.95/1.66  tff(c_700, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_61, c_697])).
% 3.95/1.66  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_670, c_700])).
% 3.95/1.66  tff(c_703, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_669])).
% 3.95/1.66  tff(c_704, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_669])).
% 3.95/1.66  tff(c_717, plain, (![B_165, A_166]: (r1_tarski(B_165, '#skF_1'(A_166, B_165)) | v3_tex_2(B_165, A_166) | ~v2_tex_2(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_719, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_717])).
% 3.95/1.66  tff(c_722, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_704, c_719])).
% 3.95/1.66  tff(c_723, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_722])).
% 3.95/1.66  tff(c_732, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_723, c_34])).
% 3.95/1.66  tff(c_741, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_703, c_732])).
% 3.95/1.66  tff(c_742, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_741])).
% 3.95/1.66  tff(c_746, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_742])).
% 3.95/1.66  tff(c_708, plain, (![A_159, B_160]: (v2_tex_2('#skF_1'(A_159, B_160), A_159) | v3_tex_2(B_160, A_159) | ~v2_tex_2(B_160, A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_710, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_708])).
% 3.95/1.66  tff(c_713, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_704, c_710])).
% 3.95/1.66  tff(c_714, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_713])).
% 3.95/1.66  tff(c_764, plain, (![B_169, A_170]: (v1_zfmisc_1(B_169) | ~v2_tex_2(B_169, A_170) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | v1_xboole_0(B_169) | ~l1_pre_topc(A_170) | ~v2_tdlat_3(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.95/1.66  tff(c_817, plain, (![A_181, B_182]: (v1_zfmisc_1('#skF_1'(A_181, B_182)) | ~v2_tex_2('#skF_1'(A_181, B_182), A_181) | v1_xboole_0('#skF_1'(A_181, B_182)) | ~v2_tdlat_3(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181) | v3_tex_2(B_182, A_181) | ~v2_tex_2(B_182, A_181) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(resolution, [status(thm)], [c_28, c_764])).
% 3.95/1.66  tff(c_821, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_714, c_817])).
% 3.95/1.66  tff(c_825, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_704, c_48, c_46, c_821])).
% 3.95/1.66  tff(c_827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_50, c_746, c_742, c_825])).
% 3.95/1.66  tff(c_828, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_741])).
% 3.95/1.66  tff(c_836, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_828, c_6])).
% 3.95/1.66  tff(c_88, plain, (![B_43, A_42]: (r1_xboole_0(B_43, A_42) | k3_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_8])).
% 3.95/1.66  tff(c_120, plain, (![B_54, A_55]: (~r1_xboole_0(B_54, A_55) | ~r1_tarski(B_54, A_55) | v1_xboole_0(B_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.95/1.66  tff(c_127, plain, (![B_43, A_42]: (~r1_tarski(B_43, A_42) | v1_xboole_0(B_43) | k3_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_88, c_120])).
% 3.95/1.66  tff(c_726, plain, (v1_xboole_0('#skF_3') | k3_xboole_0('#skF_1'('#skF_2', '#skF_3'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_723, c_127])).
% 3.95/1.66  tff(c_735, plain, (k3_xboole_0('#skF_1'('#skF_2', '#skF_3'), '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_726])).
% 3.95/1.66  tff(c_839, plain, (k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_836, c_735])).
% 3.95/1.66  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_548, c_839])).
% 3.95/1.66  tff(c_849, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 3.95/1.66  tff(c_848, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.95/1.66  tff(c_1251, plain, (![B_262, A_263]: (v2_tex_2(B_262, A_263) | ~v3_tex_2(B_262, A_263) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.66  tff(c_1254, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1251])).
% 3.95/1.66  tff(c_1257, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_848, c_1254])).
% 3.95/1.66  tff(c_1320, plain, (![B_277, A_278]: (v1_zfmisc_1(B_277) | ~v2_tex_2(B_277, A_278) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_278))) | v1_xboole_0(B_277) | ~l1_pre_topc(A_278) | ~v2_tdlat_3(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.95/1.66  tff(c_1323, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1320])).
% 3.95/1.66  tff(c_1326, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1257, c_1323])).
% 3.95/1.66  tff(c_1328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_849, c_1326])).
% 3.95/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.66  
% 3.95/1.66  Inference rules
% 3.95/1.66  ----------------------
% 3.95/1.66  #Ref     : 0
% 3.95/1.66  #Sup     : 235
% 3.95/1.66  #Fact    : 0
% 3.95/1.66  #Define  : 0
% 3.95/1.66  #Split   : 10
% 3.95/1.66  #Chain   : 0
% 3.95/1.66  #Close   : 0
% 3.95/1.66  
% 3.95/1.66  Ordering : KBO
% 3.95/1.66  
% 3.95/1.66  Simplification rules
% 3.95/1.66  ----------------------
% 3.95/1.66  #Subsume      : 129
% 3.95/1.66  #Demod        : 225
% 3.95/1.66  #Tautology    : 117
% 3.95/1.66  #SimpNegUnit  : 90
% 3.95/1.66  #BackRed      : 15
% 3.95/1.66  
% 3.95/1.66  #Partial instantiations: 0
% 3.95/1.66  #Strategies tried      : 1
% 3.95/1.66  
% 3.95/1.66  Timing (in seconds)
% 3.95/1.66  ----------------------
% 3.95/1.66  Preprocessing        : 0.32
% 3.95/1.66  Parsing              : 0.18
% 3.95/1.66  CNF conversion       : 0.02
% 3.95/1.66  Main loop            : 0.52
% 3.95/1.66  Inferencing          : 0.20
% 3.95/1.66  Reduction            : 0.15
% 3.95/1.66  Demodulation         : 0.09
% 3.95/1.66  BG Simplification    : 0.02
% 3.95/1.66  Subsumption          : 0.11
% 3.95/1.66  Abstraction          : 0.02
% 3.95/1.66  MUC search           : 0.00
% 3.95/1.66  Cooper               : 0.00
% 3.95/1.66  Total                : 0.92
% 3.95/1.66  Index Insertion      : 0.00
% 3.95/1.66  Index Deletion       : 0.00
% 3.95/1.66  Index Matching       : 0.00
% 3.95/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
