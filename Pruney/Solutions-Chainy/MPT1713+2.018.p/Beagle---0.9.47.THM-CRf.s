%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:31 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 336 expanded)
%              Number of leaves         :   34 ( 128 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 987 expanded)
%              Number of equality atoms :   10 (  45 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_50,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_84,plain,(
    ! [B_62,A_63] :
      ( l1_pre_topc(B_62)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_84])).

tff(c_99,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_90])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_96,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_87])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_24,plain,(
    ! [B_26,A_4] :
      ( r1_tarski(k2_struct_0(B_26),k2_struct_0(A_4))
      | ~ m1_pre_topc(B_26,A_4)
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [A_44] :
      ( l1_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_65,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_104,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_69])).

tff(c_38,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_129,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_38])).

tff(c_132,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_129])).

tff(c_143,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_146,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_146])).

tff(c_151,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_108,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_99,c_69])).

tff(c_137,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_38])).

tff(c_140,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_137])).

tff(c_158,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_161,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_161])).

tff(c_167,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_46,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_64,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_152,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_251,plain,(
    ! [A_74,B_75] :
      ( r1_xboole_0(u1_struct_0(A_74),u1_struct_0(B_75))
      | ~ r1_tsep_1(A_74,B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_266,plain,(
    ! [B_75] :
      ( r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_75))
      | ~ r1_tsep_1('#skF_5',B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_251])).

tff(c_354,plain,(
    ! [B_80] :
      ( r1_xboole_0(k2_struct_0('#skF_5'),u1_struct_0(B_80))
      | ~ r1_tsep_1('#skF_5',B_80)
      | ~ l1_struct_0(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_266])).

tff(c_360,plain,
    ( r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_354])).

tff(c_371,plain,(
    r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_64,c_360])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r1_tarski(B_2,A_1)
      | v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_378,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_371,c_2])).

tff(c_381,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_378])).

tff(c_384,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_381])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_96,c_48,c_384])).

tff(c_390,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_405,plain,(
    ! [B_83,A_84] :
      ( l1_pre_topc(B_83)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_411,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_405])).

tff(c_420,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_411])).

tff(c_391,plain,(
    ! [A_81] :
      ( u1_struct_0(A_81) = k2_struct_0(A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_395,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_34,c_391])).

tff(c_429,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_420,c_395])).

tff(c_440,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(u1_struct_0(A_85))
      | ~ l1_struct_0(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_443,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_440])).

tff(c_450,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_443])).

tff(c_453,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_456,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_453])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_456])).

tff(c_462,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_408,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_405])).

tff(c_417,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_408])).

tff(c_425,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_417,c_395])).

tff(c_446,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_440])).

tff(c_451,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_446])).

tff(c_479,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_451])).

tff(c_487,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_479])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_487])).

tff(c_493,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_451])).

tff(c_389,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_504,plain,(
    ! [B_88,A_89] :
      ( r1_tsep_1(B_88,A_89)
      | ~ r1_tsep_1(A_89,B_88)
      | ~ l1_struct_0(B_88)
      | ~ l1_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_506,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_389,c_504])).

tff(c_509,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_493,c_506])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:24:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.37/1.34  
% 2.37/1.34  %Foreground sorts:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Background operators:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Foreground operators:
% 2.37/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.37/1.34  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.37/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.37/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.37/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.34  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.37/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.37/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.34  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.37/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.34  
% 2.65/1.36  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.65/1.36  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.65/1.36  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 2.65/1.36  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.65/1.36  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.65/1.36  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.65/1.36  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.65/1.36  tff(f_33, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.65/1.36  tff(f_94, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.65/1.36  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.36  tff(c_50, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.36  tff(c_84, plain, (![B_62, A_63]: (l1_pre_topc(B_62) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.36  tff(c_90, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_84])).
% 2.65/1.36  tff(c_99, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_90])).
% 2.65/1.36  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.36  tff(c_87, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_84])).
% 2.65/1.36  tff(c_96, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_87])).
% 2.65/1.36  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.36  tff(c_24, plain, (![B_26, A_4]: (r1_tarski(k2_struct_0(B_26), k2_struct_0(A_4)) | ~m1_pre_topc(B_26, A_4) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.65/1.36  tff(c_34, plain, (![A_44]: (l1_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.65/1.36  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.36  tff(c_65, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.36  tff(c_69, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.65/1.36  tff(c_104, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_96, c_69])).
% 2.65/1.36  tff(c_38, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.65/1.36  tff(c_129, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_104, c_38])).
% 2.65/1.36  tff(c_132, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_129])).
% 2.65/1.36  tff(c_143, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_132])).
% 2.65/1.36  tff(c_146, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_34, c_143])).
% 2.65/1.36  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_146])).
% 2.65/1.36  tff(c_151, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_132])).
% 2.65/1.36  tff(c_52, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.36  tff(c_108, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_99, c_69])).
% 2.65/1.36  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_108, c_38])).
% 2.65/1.36  tff(c_140, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_137])).
% 2.65/1.36  tff(c_158, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_140])).
% 2.65/1.36  tff(c_161, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_34, c_158])).
% 2.65/1.36  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_161])).
% 2.65/1.36  tff(c_167, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_140])).
% 2.65/1.36  tff(c_46, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.36  tff(c_64, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_46])).
% 2.65/1.36  tff(c_152, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_132])).
% 2.65/1.36  tff(c_251, plain, (![A_74, B_75]: (r1_xboole_0(u1_struct_0(A_74), u1_struct_0(B_75)) | ~r1_tsep_1(A_74, B_75) | ~l1_struct_0(B_75) | ~l1_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.36  tff(c_266, plain, (![B_75]: (r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_75)) | ~r1_tsep_1('#skF_5', B_75) | ~l1_struct_0(B_75) | ~l1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_251])).
% 2.65/1.36  tff(c_354, plain, (![B_80]: (r1_xboole_0(k2_struct_0('#skF_5'), u1_struct_0(B_80)) | ~r1_tsep_1('#skF_5', B_80) | ~l1_struct_0(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_266])).
% 2.65/1.36  tff(c_360, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_108, c_354])).
% 2.65/1.36  tff(c_371, plain, (r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_64, c_360])).
% 2.65/1.36  tff(c_2, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1) | ~r1_tarski(B_2, A_1) | v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.36  tff(c_378, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_371, c_2])).
% 2.65/1.36  tff(c_381, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_151, c_378])).
% 2.65/1.36  tff(c_384, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_24, c_381])).
% 2.65/1.36  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_96, c_48, c_384])).
% 2.65/1.36  tff(c_390, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 2.65/1.36  tff(c_405, plain, (![B_83, A_84]: (l1_pre_topc(B_83) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.36  tff(c_411, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_405])).
% 2.65/1.36  tff(c_420, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_411])).
% 2.65/1.36  tff(c_391, plain, (![A_81]: (u1_struct_0(A_81)=k2_struct_0(A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.36  tff(c_395, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_34, c_391])).
% 2.65/1.36  tff(c_429, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_420, c_395])).
% 2.65/1.36  tff(c_440, plain, (![A_85]: (~v1_xboole_0(u1_struct_0(A_85)) | ~l1_struct_0(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.65/1.36  tff(c_443, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_429, c_440])).
% 2.65/1.36  tff(c_450, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_443])).
% 2.65/1.36  tff(c_453, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_450])).
% 2.65/1.36  tff(c_456, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_34, c_453])).
% 2.65/1.36  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_420, c_456])).
% 2.65/1.36  tff(c_462, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_450])).
% 2.65/1.36  tff(c_408, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_405])).
% 2.65/1.36  tff(c_417, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_408])).
% 2.65/1.36  tff(c_425, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_417, c_395])).
% 2.65/1.36  tff(c_446, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_425, c_440])).
% 2.65/1.36  tff(c_451, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_446])).
% 2.65/1.36  tff(c_479, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_451])).
% 2.65/1.36  tff(c_487, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_34, c_479])).
% 2.65/1.36  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_417, c_487])).
% 2.65/1.36  tff(c_493, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_451])).
% 2.65/1.36  tff(c_389, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 2.65/1.36  tff(c_504, plain, (![B_88, A_89]: (r1_tsep_1(B_88, A_89) | ~r1_tsep_1(A_89, B_88) | ~l1_struct_0(B_88) | ~l1_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.65/1.36  tff(c_506, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_389, c_504])).
% 2.65/1.36  tff(c_509, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_462, c_493, c_506])).
% 2.65/1.36  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_509])).
% 2.65/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  Inference rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Ref     : 0
% 2.65/1.36  #Sup     : 85
% 2.65/1.36  #Fact    : 0
% 2.65/1.36  #Define  : 0
% 2.65/1.36  #Split   : 12
% 2.65/1.36  #Chain   : 0
% 2.65/1.36  #Close   : 0
% 2.65/1.36  
% 2.65/1.36  Ordering : KBO
% 2.65/1.36  
% 2.65/1.36  Simplification rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Subsume      : 2
% 2.65/1.36  #Demod        : 64
% 2.65/1.36  #Tautology    : 27
% 2.65/1.36  #SimpNegUnit  : 14
% 2.65/1.36  #BackRed      : 0
% 2.65/1.36  
% 2.65/1.36  #Partial instantiations: 0
% 2.65/1.36  #Strategies tried      : 1
% 2.65/1.36  
% 2.65/1.36  Timing (in seconds)
% 2.65/1.36  ----------------------
% 2.65/1.36  Preprocessing        : 0.34
% 2.75/1.36  Parsing              : 0.17
% 2.75/1.36  CNF conversion       : 0.03
% 2.75/1.36  Main loop            : 0.25
% 2.75/1.36  Inferencing          : 0.08
% 2.75/1.36  Reduction            : 0.08
% 2.75/1.36  Demodulation         : 0.05
% 2.75/1.36  BG Simplification    : 0.02
% 2.75/1.36  Subsumption          : 0.05
% 2.75/1.36  Abstraction          : 0.02
% 2.75/1.36  MUC search           : 0.00
% 2.75/1.36  Cooper               : 0.00
% 2.75/1.36  Total                : 0.64
% 2.75/1.36  Index Insertion      : 0.00
% 2.75/1.36  Index Deletion       : 0.00
% 2.75/1.36  Index Matching       : 0.00
% 2.75/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
