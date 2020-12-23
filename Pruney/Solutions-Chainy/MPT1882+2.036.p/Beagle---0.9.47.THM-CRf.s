%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:17 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 270 expanded)
%              Number of leaves         :   29 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 (1016 expanded)
%              Number of equality atoms :    9 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_133,negated_conjecture,(
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

tff(f_81,axiom,(
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

tff(f_113,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_53,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_105,plain,(
    ! [A_53,B_54] :
      ( '#skF_3'(A_53,B_54) != B_54
      | v3_tex_2(B_54,A_53)
      | ~ v2_tex_2(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_108,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_111,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_108])).

tff(c_112,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_111])).

tff(c_113,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_55,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_52])).

tff(c_155,plain,(
    ! [B_63,A_64] :
      ( v2_tex_2(B_63,A_64)
      | ~ v1_zfmisc_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | v1_xboole_0(B_63)
      | ~ l1_pre_topc(A_64)
      | ~ v2_tdlat_3(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_161,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_165,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_55,c_161])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_113,c_165])).

tff(c_169,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_177,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,'#skF_3'(A_68,B_67))
      | v3_tex_2(B_67,A_68)
      | ~ v2_tex_2(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_179,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_177])).

tff(c_182,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_169,c_179])).

tff(c_183,plain,(
    r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_182])).

tff(c_79,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41),B_41)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | r1_xboole_0(A_43,B_42) ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( ~ r1_xboole_0(B_11,A_10)
      | ~ r1_tarski(B_11,A_10)
      | v1_xboole_0(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,(
    ! [A_43,B_42] :
      ( ~ r1_tarski(A_43,B_42)
      | v1_xboole_0(A_43)
      | ~ v1_xboole_0(B_42) ) ),
    inference(resolution,[status(thm)],[c_84,c_12])).

tff(c_189,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_183,c_88])).

tff(c_195,plain,(
    ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_189])).

tff(c_168,plain,(
    '#skF_3'('#skF_4','#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_28,plain,(
    ! [B_25,A_23] :
      ( B_25 = A_23
      | ~ r1_tarski(A_23,B_25)
      | ~ v1_zfmisc_1(B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_186,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_183,c_28])).

tff(c_192,plain,
    ( ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_168,c_186])).

tff(c_204,plain,(
    ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_192])).

tff(c_170,plain,(
    ! [A_65,B_66] :
      ( v2_tex_2('#skF_3'(A_65,B_66),A_65)
      | v3_tex_2(B_66,A_65)
      | ~ v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_172,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_175,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_169,c_172])).

tff(c_176,plain,(
    v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_175])).

tff(c_213,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1('#skF_3'(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | v3_tex_2(B_74,A_73)
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [B_28,A_26] :
      ( v1_zfmisc_1(B_28)
      | ~ v2_tex_2(B_28,A_26)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | v1_xboole_0(B_28)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_275,plain,(
    ! [A_85,B_86] :
      ( v1_zfmisc_1('#skF_3'(A_85,B_86))
      | ~ v2_tex_2('#skF_3'(A_85,B_86),A_85)
      | v1_xboole_0('#skF_3'(A_85,B_86))
      | ~ v2_tdlat_3(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85)
      | v3_tex_2(B_86,A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_213,c_32])).

tff(c_279,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_275])).

tff(c_283,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_169,c_42,c_40,c_279])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_44,c_195,c_204,c_283])).

tff(c_286,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_288,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_52])).

tff(c_333,plain,(
    ! [B_108,A_109] :
      ( v2_tex_2(B_108,A_109)
      | ~ v3_tex_2(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_336,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_333])).

tff(c_339,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_288,c_336])).

tff(c_374,plain,(
    ! [B_118,A_119] :
      ( v1_zfmisc_1(B_118)
      | ~ v2_tex_2(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | v1_xboole_0(B_118)
      | ~ l1_pre_topc(A_119)
      | ~ v2_tdlat_3(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_380,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_374])).

tff(c_384,plain,
    ( v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_339,c_380])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_286,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.56/1.33  
% 2.56/1.33  %Foreground sorts:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Background operators:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Foreground operators:
% 2.56/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.56/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.56/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.33  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.56/1.33  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.56/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.56/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.33  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.56/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.33  
% 2.56/1.34  tff(f_133, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.56/1.34  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.56/1.34  tff(f_113, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.56/1.34  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.56/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.56/1.34  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.56/1.34  tff(f_94, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.56/1.34  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_36, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_46, plain, (~v1_zfmisc_1('#skF_5') | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_53, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 2.56/1.34  tff(c_38, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_105, plain, (![A_53, B_54]: ('#skF_3'(A_53, B_54)!=B_54 | v3_tex_2(B_54, A_53) | ~v2_tex_2(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.34  tff(c_108, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_105])).
% 2.56/1.34  tff(c_111, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_108])).
% 2.56/1.34  tff(c_112, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_53, c_111])).
% 2.56/1.34  tff(c_113, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_112])).
% 2.56/1.34  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_40, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_52, plain, (v3_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.56/1.34  tff(c_55, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_53, c_52])).
% 2.56/1.34  tff(c_155, plain, (![B_63, A_64]: (v2_tex_2(B_63, A_64) | ~v1_zfmisc_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | v1_xboole_0(B_63) | ~l1_pre_topc(A_64) | ~v2_tdlat_3(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.56/1.34  tff(c_161, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_155])).
% 2.56/1.34  tff(c_165, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_55, c_161])).
% 2.56/1.34  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_113, c_165])).
% 2.56/1.34  tff(c_169, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_112])).
% 2.56/1.34  tff(c_177, plain, (![B_67, A_68]: (r1_tarski(B_67, '#skF_3'(A_68, B_67)) | v3_tex_2(B_67, A_68) | ~v2_tex_2(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.34  tff(c_179, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_177])).
% 2.56/1.34  tff(c_182, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_169, c_179])).
% 2.56/1.34  tff(c_183, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_53, c_182])).
% 2.56/1.34  tff(c_79, plain, (![A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41), B_41) | r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.34  tff(c_84, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | r1_xboole_0(A_43, B_42))), inference(resolution, [status(thm)], [c_79, c_2])).
% 2.56/1.34  tff(c_12, plain, (![B_11, A_10]: (~r1_xboole_0(B_11, A_10) | ~r1_tarski(B_11, A_10) | v1_xboole_0(B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.34  tff(c_88, plain, (![A_43, B_42]: (~r1_tarski(A_43, B_42) | v1_xboole_0(A_43) | ~v1_xboole_0(B_42))), inference(resolution, [status(thm)], [c_84, c_12])).
% 2.56/1.34  tff(c_189, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_183, c_88])).
% 2.56/1.34  tff(c_195, plain, (~v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_36, c_189])).
% 2.56/1.34  tff(c_168, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_112])).
% 2.56/1.34  tff(c_28, plain, (![B_25, A_23]: (B_25=A_23 | ~r1_tarski(A_23, B_25) | ~v1_zfmisc_1(B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.34  tff(c_186, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_183, c_28])).
% 2.56/1.34  tff(c_192, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_36, c_168, c_186])).
% 2.56/1.34  tff(c_204, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_195, c_192])).
% 2.56/1.34  tff(c_170, plain, (![A_65, B_66]: (v2_tex_2('#skF_3'(A_65, B_66), A_65) | v3_tex_2(B_66, A_65) | ~v2_tex_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.34  tff(c_172, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_170])).
% 2.56/1.34  tff(c_175, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_169, c_172])).
% 2.56/1.34  tff(c_176, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_53, c_175])).
% 2.56/1.34  tff(c_213, plain, (![A_73, B_74]: (m1_subset_1('#skF_3'(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | v3_tex_2(B_74, A_73) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.34  tff(c_32, plain, (![B_28, A_26]: (v1_zfmisc_1(B_28) | ~v2_tex_2(B_28, A_26) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | v1_xboole_0(B_28) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.56/1.34  tff(c_275, plain, (![A_85, B_86]: (v1_zfmisc_1('#skF_3'(A_85, B_86)) | ~v2_tex_2('#skF_3'(A_85, B_86), A_85) | v1_xboole_0('#skF_3'(A_85, B_86)) | ~v2_tdlat_3(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85) | v3_tex_2(B_86, A_85) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_213, c_32])).
% 2.56/1.34  tff(c_279, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_176, c_275])).
% 2.56/1.34  tff(c_283, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_169, c_42, c_40, c_279])).
% 2.56/1.34  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_44, c_195, c_204, c_283])).
% 2.56/1.34  tff(c_286, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 2.56/1.34  tff(c_288, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_286, c_52])).
% 2.56/1.34  tff(c_333, plain, (![B_108, A_109]: (v2_tex_2(B_108, A_109) | ~v3_tex_2(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.34  tff(c_336, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_333])).
% 2.56/1.34  tff(c_339, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_288, c_336])).
% 2.56/1.34  tff(c_374, plain, (![B_118, A_119]: (v1_zfmisc_1(B_118) | ~v2_tex_2(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | v1_xboole_0(B_118) | ~l1_pre_topc(A_119) | ~v2_tdlat_3(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.56/1.34  tff(c_380, plain, (v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_374])).
% 2.56/1.34  tff(c_384, plain, (v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_339, c_380])).
% 2.56/1.34  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_286, c_384])).
% 2.56/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  Inference rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Ref     : 0
% 2.56/1.34  #Sup     : 59
% 2.56/1.34  #Fact    : 0
% 2.56/1.34  #Define  : 0
% 2.56/1.34  #Split   : 3
% 2.56/1.34  #Chain   : 0
% 2.56/1.34  #Close   : 0
% 2.56/1.34  
% 2.56/1.34  Ordering : KBO
% 2.56/1.34  
% 2.56/1.34  Simplification rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Subsume      : 14
% 2.56/1.34  #Demod        : 58
% 2.56/1.34  #Tautology    : 14
% 2.56/1.34  #SimpNegUnit  : 19
% 2.56/1.34  #BackRed      : 0
% 2.56/1.34  
% 2.56/1.34  #Partial instantiations: 0
% 2.56/1.34  #Strategies tried      : 1
% 2.56/1.34  
% 2.56/1.34  Timing (in seconds)
% 2.56/1.34  ----------------------
% 2.56/1.35  Preprocessing        : 0.30
% 2.56/1.35  Parsing              : 0.16
% 2.56/1.35  CNF conversion       : 0.02
% 2.56/1.35  Main loop            : 0.28
% 2.56/1.35  Inferencing          : 0.11
% 2.56/1.35  Reduction            : 0.07
% 2.56/1.35  Demodulation         : 0.05
% 2.56/1.35  BG Simplification    : 0.02
% 2.56/1.35  Subsumption          : 0.06
% 2.56/1.35  Abstraction          : 0.01
% 2.56/1.35  MUC search           : 0.00
% 2.56/1.35  Cooper               : 0.00
% 2.56/1.35  Total                : 0.61
% 2.56/1.35  Index Insertion      : 0.00
% 2.56/1.35  Index Deletion       : 0.00
% 2.56/1.35  Index Matching       : 0.00
% 2.56/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
