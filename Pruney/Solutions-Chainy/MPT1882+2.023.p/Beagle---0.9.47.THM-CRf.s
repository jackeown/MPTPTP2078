%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:15 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 387 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  218 (1458 expanded)
%              Number of equality atoms :   20 (  86 expanded)
%              Maximal formula depth    :   17 (   4 average)
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

tff(f_143,negated_conjecture,(
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

tff(f_123,axiom,(
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

tff(f_104,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

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
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_96,plain,(
    ! [A_70,B_71] :
      ( '#skF_2'(A_70,B_71) != B_71
      | v3_tex_2(B_71,A_70)
      | ~ v2_tex_2(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_103,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_107,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_103])).

tff(c_108,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_107])).

tff(c_109,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_132,plain,(
    ! [B_76,A_77] :
      ( v2_tex_2(B_76,A_77)
      | ~ v1_zfmisc_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(B_76)
      | ~ l1_pre_topc(A_77)
      | ~ v2_tdlat_3(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_139,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_143,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54,c_139])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_109,c_143])).

tff(c_146,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_147,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_148,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,'#skF_2'(A_79,B_78))
      | v3_tex_2(B_78,A_79)
      | ~ v2_tex_2(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_153,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_148])).

tff(c_157,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_147,c_153])).

tff(c_158,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_157])).

tff(c_28,plain,(
    ! [B_44,A_42] :
      ( B_44 = A_42
      | ~ r1_tarski(A_42,B_44)
      | ~ v1_zfmisc_1(B_44)
      | v1_xboole_0(B_44)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_161,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_158,c_28])).

tff(c_167,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_146,c_161])).

tff(c_171,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_175,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_171])).

tff(c_176,plain,(
    ! [A_80,B_81] :
      ( v2_tex_2('#skF_2'(A_80,B_81),A_80)
      | v3_tex_2(B_81,A_80)
      | ~ v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_181,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_176])).

tff(c_185,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_147,c_181])).

tff(c_186,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_185])).

tff(c_20,plain,(
    ! [A_30,B_36] :
      ( m1_subset_1('#skF_2'(A_30,B_36),k1_zfmisc_1(u1_struct_0(A_30)))
      | v3_tex_2(B_36,A_30)
      | ~ v2_tex_2(B_36,A_30)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_205,plain,(
    ! [B_84,A_85] :
      ( v1_zfmisc_1(B_84)
      | ~ v2_tex_2(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_xboole_0(B_84)
      | ~ l1_pre_topc(A_85)
      | ~ v2_tdlat_3(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_359,plain,(
    ! [A_135,B_136] :
      ( v1_zfmisc_1('#skF_2'(A_135,B_136))
      | ~ v2_tex_2('#skF_2'(A_135,B_136),A_135)
      | v1_xboole_0('#skF_2'(A_135,B_136))
      | ~ v2_tdlat_3(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135)
      | v3_tex_2(B_136,A_135)
      | ~ v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_20,c_205])).

tff(c_365,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_359])).

tff(c_372,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_147,c_42,c_40,c_365])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_175,c_171,c_372])).

tff(c_375,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_2,B_3] : m1_subset_1(k6_subset_1(A_2,B_3),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ v1_xboole_0(C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_59,A_60,B_61] :
      ( ~ v1_xboole_0(A_59)
      | ~ r2_hidden(A_60,k6_subset_1(A_59,B_61)) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_80,plain,(
    ! [A_59,B_61] :
      ( ~ v1_xboole_0(A_59)
      | k6_subset_1(A_59,B_61) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_379,plain,(
    ! [B_61] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_375,c_80])).

tff(c_26,plain,(
    ! [B_41,A_40] :
      ( k6_subset_1(B_41,A_40) != k1_xboole_0
      | B_41 = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_164,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_158,c_26])).

tff(c_170,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_164])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_170])).

tff(c_384,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_383,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_417,plain,(
    ! [B_153,A_154] :
      ( v2_tex_2(B_153,A_154)
      | ~ v3_tex_2(B_153,A_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_424,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_417])).

tff(c_428,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_383,c_424])).

tff(c_497,plain,(
    ! [B_167,A_168] :
      ( v1_zfmisc_1(B_167)
      | ~ v2_tex_2(B_167,A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | v1_xboole_0(B_167)
      | ~ l1_pre_topc(A_168)
      | ~ v2_tdlat_3(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_507,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_497])).

tff(c_512,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_428,c_507])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_384,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 12:26:08 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.35  
% 2.83/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.35  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.83/1.35  
% 2.83/1.35  %Foreground sorts:
% 2.83/1.35  
% 2.83/1.35  
% 2.83/1.35  %Background operators:
% 2.83/1.35  
% 2.83/1.35  
% 2.83/1.35  %Foreground operators:
% 2.83/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.35  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.83/1.35  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.83/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.83/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.35  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.83/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.35  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.83/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.35  
% 2.91/1.37  tff(f_143, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.91/1.37  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.91/1.37  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.91/1.37  tff(f_123, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.91/1.37  tff(f_104, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.91/1.37  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.91/1.37  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.91/1.37  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.91/1.37  tff(f_91, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 2.91/1.37  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_52, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_54, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.91/1.37  tff(c_46, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_56, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46])).
% 2.91/1.37  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.37  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_96, plain, (![A_70, B_71]: ('#skF_2'(A_70, B_71)!=B_71 | v3_tex_2(B_71, A_70) | ~v2_tex_2(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.91/1.37  tff(c_103, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_96])).
% 2.91/1.37  tff(c_107, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_103])).
% 2.91/1.37  tff(c_108, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_107])).
% 2.91/1.37  tff(c_109, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_108])).
% 2.91/1.37  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_40, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.91/1.37  tff(c_132, plain, (![B_76, A_77]: (v2_tex_2(B_76, A_77) | ~v1_zfmisc_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(B_76) | ~l1_pre_topc(A_77) | ~v2_tdlat_3(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.91/1.37  tff(c_139, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_132])).
% 2.91/1.37  tff(c_143, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54, c_139])).
% 2.91/1.37  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_109, c_143])).
% 2.91/1.37  tff(c_146, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_108])).
% 2.91/1.37  tff(c_147, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_108])).
% 2.91/1.37  tff(c_148, plain, (![B_78, A_79]: (r1_tarski(B_78, '#skF_2'(A_79, B_78)) | v3_tex_2(B_78, A_79) | ~v2_tex_2(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.91/1.37  tff(c_153, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_148])).
% 2.91/1.37  tff(c_157, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_147, c_153])).
% 2.91/1.37  tff(c_158, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_157])).
% 2.91/1.37  tff(c_28, plain, (![B_44, A_42]: (B_44=A_42 | ~r1_tarski(A_42, B_44) | ~v1_zfmisc_1(B_44) | v1_xboole_0(B_44) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.91/1.37  tff(c_161, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_158, c_28])).
% 2.91/1.37  tff(c_167, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_146, c_161])).
% 2.91/1.37  tff(c_171, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_167])).
% 2.91/1.37  tff(c_175, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_171])).
% 2.91/1.37  tff(c_176, plain, (![A_80, B_81]: (v2_tex_2('#skF_2'(A_80, B_81), A_80) | v3_tex_2(B_81, A_80) | ~v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.91/1.37  tff(c_181, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_176])).
% 2.91/1.37  tff(c_185, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_147, c_181])).
% 2.91/1.37  tff(c_186, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_185])).
% 2.91/1.37  tff(c_20, plain, (![A_30, B_36]: (m1_subset_1('#skF_2'(A_30, B_36), k1_zfmisc_1(u1_struct_0(A_30))) | v3_tex_2(B_36, A_30) | ~v2_tex_2(B_36, A_30) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.91/1.37  tff(c_205, plain, (![B_84, A_85]: (v1_zfmisc_1(B_84) | ~v2_tex_2(B_84, A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | v1_xboole_0(B_84) | ~l1_pre_topc(A_85) | ~v2_tdlat_3(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.91/1.37  tff(c_359, plain, (![A_135, B_136]: (v1_zfmisc_1('#skF_2'(A_135, B_136)) | ~v2_tex_2('#skF_2'(A_135, B_136), A_135) | v1_xboole_0('#skF_2'(A_135, B_136)) | ~v2_tdlat_3(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135) | v3_tex_2(B_136, A_135) | ~v2_tex_2(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_20, c_205])).
% 2.91/1.37  tff(c_365, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_186, c_359])).
% 2.91/1.37  tff(c_372, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_147, c_42, c_40, c_365])).
% 2.91/1.37  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_175, c_171, c_372])).
% 2.91/1.37  tff(c_375, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_167])).
% 2.91/1.37  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.91/1.37  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k6_subset_1(A_2, B_3), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.37  tff(c_66, plain, (![C_54, B_55, A_56]: (~v1_xboole_0(C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.37  tff(c_75, plain, (![A_59, A_60, B_61]: (~v1_xboole_0(A_59) | ~r2_hidden(A_60, k6_subset_1(A_59, B_61)))), inference(resolution, [status(thm)], [c_4, c_66])).
% 2.91/1.37  tff(c_80, plain, (![A_59, B_61]: (~v1_xboole_0(A_59) | k6_subset_1(A_59, B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.91/1.37  tff(c_379, plain, (![B_61]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_375, c_80])).
% 2.91/1.37  tff(c_26, plain, (![B_41, A_40]: (k6_subset_1(B_41, A_40)!=k1_xboole_0 | B_41=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.91/1.37  tff(c_164, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_158, c_26])).
% 2.91/1.37  tff(c_170, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_146, c_164])).
% 2.91/1.37  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_379, c_170])).
% 2.91/1.37  tff(c_384, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.91/1.37  tff(c_383, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 2.91/1.37  tff(c_417, plain, (![B_153, A_154]: (v2_tex_2(B_153, A_154) | ~v3_tex_2(B_153, A_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.91/1.37  tff(c_424, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_417])).
% 2.91/1.37  tff(c_428, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_383, c_424])).
% 2.91/1.37  tff(c_497, plain, (![B_167, A_168]: (v1_zfmisc_1(B_167) | ~v2_tex_2(B_167, A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | v1_xboole_0(B_167) | ~l1_pre_topc(A_168) | ~v2_tdlat_3(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.91/1.37  tff(c_507, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_497])).
% 2.91/1.37  tff(c_512, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_428, c_507])).
% 2.91/1.37  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_384, c_512])).
% 2.91/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.37  
% 2.91/1.37  Inference rules
% 2.91/1.37  ----------------------
% 2.91/1.37  #Ref     : 0
% 2.91/1.37  #Sup     : 83
% 2.91/1.37  #Fact    : 0
% 2.91/1.37  #Define  : 0
% 2.91/1.37  #Split   : 6
% 2.91/1.37  #Chain   : 0
% 2.91/1.37  #Close   : 0
% 2.91/1.37  
% 2.91/1.37  Ordering : KBO
% 2.91/1.37  
% 2.91/1.37  Simplification rules
% 2.91/1.37  ----------------------
% 2.91/1.37  #Subsume      : 12
% 2.91/1.37  #Demod        : 63
% 2.91/1.37  #Tautology    : 12
% 2.91/1.37  #SimpNegUnit  : 17
% 2.91/1.37  #BackRed      : 1
% 2.91/1.37  
% 2.91/1.37  #Partial instantiations: 0
% 2.91/1.37  #Strategies tried      : 1
% 2.91/1.37  
% 2.91/1.37  Timing (in seconds)
% 2.91/1.37  ----------------------
% 2.91/1.37  Preprocessing        : 0.31
% 2.91/1.37  Parsing              : 0.18
% 2.91/1.37  CNF conversion       : 0.02
% 2.91/1.37  Main loop            : 0.32
% 2.91/1.37  Inferencing          : 0.12
% 2.91/1.37  Reduction            : 0.08
% 2.91/1.37  Demodulation         : 0.06
% 2.91/1.37  BG Simplification    : 0.02
% 2.91/1.37  Subsumption          : 0.07
% 2.91/1.37  Abstraction          : 0.02
% 2.91/1.37  MUC search           : 0.00
% 2.91/1.37  Cooper               : 0.00
% 2.91/1.38  Total                : 0.67
% 2.91/1.38  Index Insertion      : 0.00
% 2.91/1.38  Index Deletion       : 0.00
% 2.91/1.38  Index Matching       : 0.00
% 2.91/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
