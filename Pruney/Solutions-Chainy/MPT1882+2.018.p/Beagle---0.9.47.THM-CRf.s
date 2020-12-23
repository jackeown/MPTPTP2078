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
% DateTime   : Thu Dec  3 10:30:15 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 387 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  213 (1453 expanded)
%              Number of equality atoms :   20 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_132,negated_conjecture,(
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

tff(f_72,axiom,(
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

tff(f_112,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_97,plain,(
    ! [A_51,B_52] :
      ( '#skF_2'(A_51,B_52) != B_52
      | v3_tex_2(B_52,A_51)
      | ~ v2_tex_2(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_104,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_108,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104])).

tff(c_109,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_108])).

tff(c_110,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_168,plain,(
    ! [B_61,A_62] :
      ( v2_tex_2(B_61,A_62)
      | ~ v1_zfmisc_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | v1_xboole_0(B_61)
      | ~ l1_pre_topc(A_62)
      | ~ v2_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_178,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_183,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54,c_178])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_110,c_183])).

tff(c_186,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_187,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_199,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,'#skF_2'(A_66,B_65))
      | v3_tex_2(B_65,A_66)
      | ~ v2_tex_2(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_204,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_199])).

tff(c_208,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_187,c_204])).

tff(c_209,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_208])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( B_24 = A_22
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_212,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_209,c_28])).

tff(c_218,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_186,c_212])).

tff(c_222,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_226,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_222])).

tff(c_188,plain,(
    ! [A_63,B_64] :
      ( v2_tex_2('#skF_2'(A_63,B_64),A_63)
      | v3_tex_2(B_64,A_63)
      | ~ v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_193,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_188])).

tff(c_197,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_187,c_193])).

tff(c_198,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_197])).

tff(c_20,plain,(
    ! [A_10,B_16] :
      ( m1_subset_1('#skF_2'(A_10,B_16),k1_zfmisc_1(u1_struct_0(A_10)))
      | v3_tex_2(B_16,A_10)
      | ~ v2_tex_2(B_16,A_10)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_245,plain,(
    ! [B_69,A_70] :
      ( v1_zfmisc_1(B_69)
      | ~ v2_tex_2(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | v1_xboole_0(B_69)
      | ~ l1_pre_topc(A_70)
      | ~ v2_tdlat_3(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_361,plain,(
    ! [A_98,B_99] :
      ( v1_zfmisc_1('#skF_2'(A_98,B_99))
      | ~ v2_tex_2('#skF_2'(A_98,B_99),A_98)
      | v1_xboole_0('#skF_2'(A_98,B_99))
      | ~ v2_tdlat_3(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98)
      | v3_tex_2(B_99,A_98)
      | ~ v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_20,c_245])).

tff(c_367,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_361])).

tff(c_374,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_187,c_42,c_40,c_367])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_226,c_222,c_374])).

tff(c_377,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_2,B_3] : m1_subset_1(k6_subset_1(A_2,B_3),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [C_35,B_36,A_37] :
      ( ~ v1_xboole_0(C_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_40,A_41,B_42] :
      ( ~ v1_xboole_0(A_40)
      | ~ r2_hidden(A_41,k6_subset_1(A_40,B_42)) ) ),
    inference(resolution,[status(thm)],[c_4,c_67])).

tff(c_81,plain,(
    ! [A_40,B_42] :
      ( ~ v1_xboole_0(A_40)
      | k6_subset_1(A_40,B_42) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_381,plain,(
    ! [B_42] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_377,c_81])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k6_subset_1(B_21,A_20) != k1_xboole_0
      | B_21 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_215,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_209,c_26])).

tff(c_221,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_215])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_221])).

tff(c_386,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_385,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_420,plain,(
    ! [B_117,A_118] :
      ( v2_tex_2(B_117,A_118)
      | ~ v3_tex_2(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_427,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_420])).

tff(c_431,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_385,c_427])).

tff(c_483,plain,(
    ! [B_129,A_130] :
      ( v1_zfmisc_1(B_129)
      | ~ v2_tex_2(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | v1_xboole_0(B_129)
      | ~ l1_pre_topc(A_130)
      | ~ v2_tdlat_3(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_493,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_483])).

tff(c_498,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_431,c_493])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_386,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:42:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.44  
% 3.05/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.45  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.05/1.45  
% 3.05/1.45  %Foreground sorts:
% 3.05/1.45  
% 3.05/1.45  
% 3.05/1.45  %Background operators:
% 3.05/1.45  
% 3.05/1.45  
% 3.05/1.45  %Foreground operators:
% 3.05/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.05/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.05/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.45  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.05/1.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.05/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.45  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.05/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.45  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.05/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.05/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.45  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.05/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.45  
% 3.05/1.47  tff(f_132, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.05/1.47  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.05/1.47  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.05/1.47  tff(f_112, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.05/1.47  tff(f_93, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.05/1.47  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.05/1.47  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.05/1.47  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.05/1.47  tff(f_80, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 3.05/1.47  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_52, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_54, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 3.05/1.47  tff(c_46, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_56, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46])).
% 3.05/1.47  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.05/1.47  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_97, plain, (![A_51, B_52]: ('#skF_2'(A_51, B_52)!=B_52 | v3_tex_2(B_52, A_51) | ~v2_tex_2(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.05/1.47  tff(c_104, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_97])).
% 3.05/1.47  tff(c_108, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104])).
% 3.05/1.47  tff(c_109, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_108])).
% 3.05/1.47  tff(c_110, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_109])).
% 3.05/1.47  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_40, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.05/1.47  tff(c_168, plain, (![B_61, A_62]: (v2_tex_2(B_61, A_62) | ~v1_zfmisc_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | v1_xboole_0(B_61) | ~l1_pre_topc(A_62) | ~v2_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.05/1.47  tff(c_178, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_168])).
% 3.05/1.47  tff(c_183, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54, c_178])).
% 3.05/1.47  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_110, c_183])).
% 3.05/1.47  tff(c_186, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_109])).
% 3.05/1.47  tff(c_187, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_109])).
% 3.05/1.47  tff(c_199, plain, (![B_65, A_66]: (r1_tarski(B_65, '#skF_2'(A_66, B_65)) | v3_tex_2(B_65, A_66) | ~v2_tex_2(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.05/1.47  tff(c_204, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_199])).
% 3.05/1.47  tff(c_208, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_187, c_204])).
% 3.05/1.47  tff(c_209, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_208])).
% 3.05/1.47  tff(c_28, plain, (![B_24, A_22]: (B_24=A_22 | ~r1_tarski(A_22, B_24) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.47  tff(c_212, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_209, c_28])).
% 3.05/1.47  tff(c_218, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_186, c_212])).
% 3.05/1.47  tff(c_222, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_218])).
% 3.05/1.47  tff(c_226, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_222])).
% 3.05/1.47  tff(c_188, plain, (![A_63, B_64]: (v2_tex_2('#skF_2'(A_63, B_64), A_63) | v3_tex_2(B_64, A_63) | ~v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.05/1.47  tff(c_193, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_188])).
% 3.05/1.47  tff(c_197, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_187, c_193])).
% 3.05/1.47  tff(c_198, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_197])).
% 3.05/1.47  tff(c_20, plain, (![A_10, B_16]: (m1_subset_1('#skF_2'(A_10, B_16), k1_zfmisc_1(u1_struct_0(A_10))) | v3_tex_2(B_16, A_10) | ~v2_tex_2(B_16, A_10) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.05/1.47  tff(c_245, plain, (![B_69, A_70]: (v1_zfmisc_1(B_69) | ~v2_tex_2(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | v1_xboole_0(B_69) | ~l1_pre_topc(A_70) | ~v2_tdlat_3(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.05/1.47  tff(c_361, plain, (![A_98, B_99]: (v1_zfmisc_1('#skF_2'(A_98, B_99)) | ~v2_tex_2('#skF_2'(A_98, B_99), A_98) | v1_xboole_0('#skF_2'(A_98, B_99)) | ~v2_tdlat_3(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98) | v3_tex_2(B_99, A_98) | ~v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_20, c_245])).
% 3.05/1.47  tff(c_367, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_198, c_361])).
% 3.05/1.47  tff(c_374, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_187, c_42, c_40, c_367])).
% 3.05/1.47  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_226, c_222, c_374])).
% 3.05/1.47  tff(c_377, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_218])).
% 3.05/1.47  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.05/1.47  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k6_subset_1(A_2, B_3), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.47  tff(c_67, plain, (![C_35, B_36, A_37]: (~v1_xboole_0(C_35) | ~m1_subset_1(B_36, k1_zfmisc_1(C_35)) | ~r2_hidden(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.47  tff(c_76, plain, (![A_40, A_41, B_42]: (~v1_xboole_0(A_40) | ~r2_hidden(A_41, k6_subset_1(A_40, B_42)))), inference(resolution, [status(thm)], [c_4, c_67])).
% 3.05/1.47  tff(c_81, plain, (![A_40, B_42]: (~v1_xboole_0(A_40) | k6_subset_1(A_40, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_76])).
% 3.05/1.47  tff(c_381, plain, (![B_42]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_377, c_81])).
% 3.05/1.47  tff(c_26, plain, (![B_21, A_20]: (k6_subset_1(B_21, A_20)!=k1_xboole_0 | B_21=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.05/1.47  tff(c_215, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_209, c_26])).
% 3.05/1.47  tff(c_221, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_186, c_215])).
% 3.05/1.47  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_381, c_221])).
% 3.05/1.47  tff(c_386, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.05/1.47  tff(c_385, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.05/1.47  tff(c_420, plain, (![B_117, A_118]: (v2_tex_2(B_117, A_118) | ~v3_tex_2(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.05/1.47  tff(c_427, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_420])).
% 3.05/1.47  tff(c_431, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_385, c_427])).
% 3.05/1.47  tff(c_483, plain, (![B_129, A_130]: (v1_zfmisc_1(B_129) | ~v2_tex_2(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | v1_xboole_0(B_129) | ~l1_pre_topc(A_130) | ~v2_tdlat_3(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.05/1.47  tff(c_493, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_483])).
% 3.05/1.47  tff(c_498, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_431, c_493])).
% 3.05/1.47  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_386, c_498])).
% 3.05/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.47  
% 3.05/1.47  Inference rules
% 3.05/1.47  ----------------------
% 3.05/1.47  #Ref     : 0
% 3.05/1.47  #Sup     : 81
% 3.05/1.47  #Fact    : 0
% 3.05/1.47  #Define  : 0
% 3.05/1.47  #Split   : 6
% 3.05/1.47  #Chain   : 0
% 3.05/1.47  #Close   : 0
% 3.05/1.47  
% 3.05/1.47  Ordering : KBO
% 3.05/1.47  
% 3.05/1.47  Simplification rules
% 3.05/1.47  ----------------------
% 3.05/1.47  #Subsume      : 13
% 3.05/1.47  #Demod        : 63
% 3.05/1.47  #Tautology    : 12
% 3.05/1.47  #SimpNegUnit  : 17
% 3.05/1.47  #BackRed      : 1
% 3.05/1.47  
% 3.05/1.47  #Partial instantiations: 0
% 3.05/1.47  #Strategies tried      : 1
% 3.05/1.47  
% 3.05/1.47  Timing (in seconds)
% 3.05/1.47  ----------------------
% 3.20/1.47  Preprocessing        : 0.32
% 3.20/1.47  Parsing              : 0.18
% 3.20/1.47  CNF conversion       : 0.02
% 3.20/1.47  Main loop            : 0.36
% 3.20/1.47  Inferencing          : 0.14
% 3.20/1.47  Reduction            : 0.10
% 3.20/1.47  Demodulation         : 0.06
% 3.20/1.47  BG Simplification    : 0.02
% 3.20/1.47  Subsumption          : 0.07
% 3.20/1.47  Abstraction          : 0.02
% 3.20/1.47  MUC search           : 0.00
% 3.20/1.47  Cooper               : 0.00
% 3.20/1.47  Total                : 0.73
% 3.20/1.47  Index Insertion      : 0.00
% 3.20/1.47  Index Deletion       : 0.00
% 3.20/1.47  Index Matching       : 0.00
% 3.20/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
