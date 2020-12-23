%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:15 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 387 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1455 expanded)
%              Number of equality atoms :   21 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k3_mcart_1 > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

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
    ! [A_74,B_75] :
      ( '#skF_2'(A_74,B_75) != B_75
      | v3_tex_2(B_75,A_74)
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
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

tff(c_162,plain,(
    ! [B_84,A_85] :
      ( v2_tex_2(B_84,A_85)
      | ~ v1_zfmisc_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_xboole_0(B_84)
      | ~ l1_pre_topc(A_85)
      | ~ v2_tdlat_3(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_172,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_162])).

tff(c_177,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_56,c_172])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_120,c_177])).

tff(c_180,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_181,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_194,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(B_90,'#skF_2'(A_91,B_90))
      | v3_tex_2(B_90,A_91)
      | ~ v2_tex_2(B_90,A_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_199,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_194])).

tff(c_203,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_181,c_199])).

tff(c_204,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_203])).

tff(c_30,plain,(
    ! [B_36,A_34] :
      ( B_36 = A_34
      | ~ r1_tarski(A_34,B_36)
      | ~ v1_zfmisc_1(B_36)
      | v1_xboole_0(B_36)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_207,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_204,c_30])).

tff(c_213,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_180,c_207])).

tff(c_217,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_221,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_217])).

tff(c_182,plain,(
    ! [A_86,B_87] :
      ( v2_tex_2('#skF_2'(A_86,B_87),A_86)
      | v3_tex_2(B_87,A_86)
      | ~ v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_187,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_191,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_181,c_187])).

tff(c_192,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_191])).

tff(c_235,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1('#skF_2'(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | v3_tex_2(B_95,A_94)
      | ~ v2_tex_2(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [B_39,A_37] :
      ( v1_zfmisc_1(B_39)
      | ~ v2_tex_2(B_39,A_37)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_37)))
      | v1_xboole_0(B_39)
      | ~ l1_pre_topc(A_37)
      | ~ v2_tdlat_3(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_356,plain,(
    ! [A_123,B_124] :
      ( v1_zfmisc_1('#skF_2'(A_123,B_124))
      | ~ v2_tex_2('#skF_2'(A_123,B_124),A_123)
      | v1_xboole_0('#skF_2'(A_123,B_124))
      | ~ v2_tdlat_3(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123)
      | v3_tex_2(B_124,A_123)
      | ~ v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_235,c_34])).

tff(c_362,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_192,c_356])).

tff(c_369,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_181,c_44,c_42,c_362])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_221,c_217,c_369])).

tff(c_372,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_8,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_2,B_3] : m1_subset_1(k6_subset_1(A_2,B_3),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_55,A_56,B_57] :
      ( ~ v1_xboole_0(A_55)
      | ~ r2_hidden(A_56,k6_subset_1(A_55,B_57)) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_86,plain,(
    ! [A_55,B_57] :
      ( ~ v1_xboole_0(A_55)
      | k6_subset_1(A_55,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_376,plain,(
    ! [B_57] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_372,c_86])).

tff(c_28,plain,(
    ! [B_33,A_32] :
      ( k6_subset_1(B_33,A_32) != k1_xboole_0
      | B_33 = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_210,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_204,c_28])).

tff(c_216,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_210])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_216])).

tff(c_381,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_380,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_424,plain,(
    ! [B_155,A_156] :
      ( v2_tex_2(B_155,A_156)
      | ~ v3_tex_2(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_431,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_424])).

tff(c_435,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_380,c_431])).

tff(c_469,plain,(
    ! [B_165,A_166] :
      ( v1_zfmisc_1(B_165)
      | ~ v2_tex_2(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | v1_xboole_0(B_165)
      | ~ l1_pre_topc(A_166)
      | ~ v2_tdlat_3(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_476,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_469])).

tff(c_480,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_435,c_476])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_381,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:34:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.39  
% 2.80/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.39  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k3_mcart_1 > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.80/1.39  
% 2.80/1.39  %Foreground sorts:
% 2.80/1.39  
% 2.80/1.39  
% 2.80/1.39  %Background operators:
% 2.80/1.39  
% 2.80/1.39  
% 2.80/1.39  %Foreground operators:
% 2.80/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.39  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.80/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.80/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.80/1.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.80/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.80/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.80/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.39  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.80/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.39  
% 2.80/1.41  tff(f_138, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.80/1.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.80/1.41  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.80/1.41  tff(f_118, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.80/1.41  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.80/1.41  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.80/1.41  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.80/1.41  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.80/1.41  tff(f_86, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 2.80/1.41  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_38, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_54, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_56, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 2.80/1.41  tff(c_48, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_58, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 2.80/1.41  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.41  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_107, plain, (![A_74, B_75]: ('#skF_2'(A_74, B_75)!=B_75 | v3_tex_2(B_75, A_74) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.41  tff(c_114, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_107])).
% 2.80/1.41  tff(c_118, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_114])).
% 2.80/1.41  tff(c_119, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_118])).
% 2.80/1.41  tff(c_120, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_119])).
% 2.80/1.41  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_42, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.80/1.41  tff(c_162, plain, (![B_84, A_85]: (v2_tex_2(B_84, A_85) | ~v1_zfmisc_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | v1_xboole_0(B_84) | ~l1_pre_topc(A_85) | ~v2_tdlat_3(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.41  tff(c_172, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_162])).
% 2.80/1.41  tff(c_177, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_56, c_172])).
% 2.80/1.41  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_120, c_177])).
% 2.80/1.41  tff(c_180, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_119])).
% 2.80/1.41  tff(c_181, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_119])).
% 2.80/1.41  tff(c_194, plain, (![B_90, A_91]: (r1_tarski(B_90, '#skF_2'(A_91, B_90)) | v3_tex_2(B_90, A_91) | ~v2_tex_2(B_90, A_91) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.41  tff(c_199, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_194])).
% 2.80/1.41  tff(c_203, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_181, c_199])).
% 2.80/1.41  tff(c_204, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_203])).
% 2.80/1.41  tff(c_30, plain, (![B_36, A_34]: (B_36=A_34 | ~r1_tarski(A_34, B_36) | ~v1_zfmisc_1(B_36) | v1_xboole_0(B_36) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.41  tff(c_207, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_204, c_30])).
% 2.80/1.41  tff(c_213, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_180, c_207])).
% 2.80/1.41  tff(c_217, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_213])).
% 2.80/1.41  tff(c_221, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_217])).
% 2.80/1.41  tff(c_182, plain, (![A_86, B_87]: (v2_tex_2('#skF_2'(A_86, B_87), A_86) | v3_tex_2(B_87, A_86) | ~v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.41  tff(c_187, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_182])).
% 2.80/1.41  tff(c_191, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_181, c_187])).
% 2.80/1.41  tff(c_192, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_191])).
% 2.80/1.41  tff(c_235, plain, (![A_94, B_95]: (m1_subset_1('#skF_2'(A_94, B_95), k1_zfmisc_1(u1_struct_0(A_94))) | v3_tex_2(B_95, A_94) | ~v2_tex_2(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.41  tff(c_34, plain, (![B_39, A_37]: (v1_zfmisc_1(B_39) | ~v2_tex_2(B_39, A_37) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_37))) | v1_xboole_0(B_39) | ~l1_pre_topc(A_37) | ~v2_tdlat_3(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.41  tff(c_356, plain, (![A_123, B_124]: (v1_zfmisc_1('#skF_2'(A_123, B_124)) | ~v2_tex_2('#skF_2'(A_123, B_124), A_123) | v1_xboole_0('#skF_2'(A_123, B_124)) | ~v2_tdlat_3(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123) | v3_tex_2(B_124, A_123) | ~v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_235, c_34])).
% 2.80/1.41  tff(c_362, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_192, c_356])).
% 2.80/1.41  tff(c_369, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_181, c_44, c_42, c_362])).
% 2.80/1.41  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_221, c_217, c_369])).
% 2.80/1.41  tff(c_372, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_213])).
% 2.80/1.41  tff(c_8, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.80/1.41  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k6_subset_1(A_2, B_3), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.41  tff(c_69, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.41  tff(c_81, plain, (![A_55, A_56, B_57]: (~v1_xboole_0(A_55) | ~r2_hidden(A_56, k6_subset_1(A_55, B_57)))), inference(resolution, [status(thm)], [c_4, c_69])).
% 2.80/1.41  tff(c_86, plain, (![A_55, B_57]: (~v1_xboole_0(A_55) | k6_subset_1(A_55, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_81])).
% 2.80/1.41  tff(c_376, plain, (![B_57]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_372, c_86])).
% 2.80/1.41  tff(c_28, plain, (![B_33, A_32]: (k6_subset_1(B_33, A_32)!=k1_xboole_0 | B_33=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.80/1.41  tff(c_210, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_204, c_28])).
% 2.80/1.41  tff(c_216, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_180, c_210])).
% 2.80/1.41  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_216])).
% 2.80/1.41  tff(c_381, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.80/1.41  tff(c_380, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 2.80/1.41  tff(c_424, plain, (![B_155, A_156]: (v2_tex_2(B_155, A_156) | ~v3_tex_2(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.41  tff(c_431, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_424])).
% 2.80/1.41  tff(c_435, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_380, c_431])).
% 2.80/1.41  tff(c_469, plain, (![B_165, A_166]: (v1_zfmisc_1(B_165) | ~v2_tex_2(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | v1_xboole_0(B_165) | ~l1_pre_topc(A_166) | ~v2_tdlat_3(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.41  tff(c_476, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_469])).
% 2.80/1.41  tff(c_480, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_435, c_476])).
% 2.80/1.41  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_381, c_480])).
% 2.80/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  
% 2.80/1.41  Inference rules
% 2.80/1.41  ----------------------
% 2.80/1.41  #Ref     : 0
% 2.80/1.41  #Sup     : 76
% 2.80/1.41  #Fact    : 0
% 2.80/1.41  #Define  : 0
% 2.80/1.41  #Split   : 6
% 2.80/1.41  #Chain   : 0
% 2.80/1.41  #Close   : 0
% 2.80/1.41  
% 2.80/1.41  Ordering : KBO
% 2.80/1.41  
% 2.80/1.41  Simplification rules
% 2.80/1.41  ----------------------
% 2.80/1.41  #Subsume      : 11
% 2.80/1.41  #Demod        : 59
% 2.80/1.41  #Tautology    : 12
% 2.80/1.41  #SimpNegUnit  : 16
% 2.80/1.41  #BackRed      : 1
% 2.80/1.41  
% 2.80/1.41  #Partial instantiations: 0
% 2.80/1.41  #Strategies tried      : 1
% 2.80/1.41  
% 2.80/1.41  Timing (in seconds)
% 2.80/1.41  ----------------------
% 2.80/1.41  Preprocessing        : 0.32
% 2.80/1.41  Parsing              : 0.17
% 2.80/1.41  CNF conversion       : 0.02
% 2.80/1.41  Main loop            : 0.32
% 2.80/1.41  Inferencing          : 0.13
% 2.80/1.41  Reduction            : 0.09
% 2.80/1.41  Demodulation         : 0.06
% 2.80/1.41  BG Simplification    : 0.02
% 2.80/1.41  Subsumption          : 0.06
% 2.80/1.41  Abstraction          : 0.01
% 2.80/1.41  MUC search           : 0.00
% 2.80/1.41  Cooper               : 0.00
% 2.80/1.41  Total                : 0.68
% 2.80/1.41  Index Insertion      : 0.00
% 2.80/1.41  Index Deletion       : 0.00
% 2.80/1.41  Index Matching       : 0.00
% 2.80/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
