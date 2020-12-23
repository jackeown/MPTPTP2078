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
% DateTime   : Thu Dec  3 10:26:35 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 342 expanded)
%              Number of leaves         :   35 ( 124 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 (1224 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_735,plain,(
    ! [B_132,A_133] :
      ( l1_pre_topc(B_132)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_738,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_735])).

tff(c_750,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_738])).

tff(c_40,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_741,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_735])).

tff(c_753,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_741])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_633,plain,(
    ! [B_116,A_117] :
      ( l1_pre_topc(B_116)
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_645,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_633])).

tff(c_655,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_645])).

tff(c_636,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_633])).

tff(c_648,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_636])).

tff(c_96,plain,(
    ! [B_74,A_75] :
      ( l1_pre_topc(B_74)
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_108,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_96])).

tff(c_118,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_108])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_96])).

tff(c_114,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ! [B_29,A_7] :
      ( r1_tarski(k2_struct_0(B_29),k2_struct_0(A_7))
      | ~ m1_pre_topc(B_29,A_7)
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_96])).

tff(c_111,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_99])).

tff(c_50,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_80,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_147,plain,(
    ! [B_82,A_83] :
      ( r1_tsep_1(B_82,A_83)
      | ~ r1_tsep_1(A_83,B_82)
      | ~ l1_struct_0(B_82)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_150,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_147])).

tff(c_151,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_154,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_154])).

tff(c_159,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_166,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_166])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_170])).

tff(c_176,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_75,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_122,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_111,c_79])).

tff(c_160,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_130,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_118,c_79])).

tff(c_251,plain,(
    ! [A_91,B_92] :
      ( r1_xboole_0(u1_struct_0(A_91),u1_struct_0(B_92))
      | ~ r1_tsep_1(A_91,B_92)
      | ~ l1_struct_0(B_92)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_266,plain,(
    ! [B_92] :
      ( r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_92))
      | ~ r1_tsep_1('#skF_6',B_92)
      | ~ l1_struct_0(B_92)
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_251])).

tff(c_359,plain,(
    ! [B_96] :
      ( r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_96))
      | ~ r1_tsep_1('#skF_6',B_96)
      | ~ l1_struct_0(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_266])).

tff(c_374,plain,
    ( r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'))
    | ~ r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_359])).

tff(c_384,plain,(
    r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_80,c_374])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = A_4
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_393,plain,(
    k4_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_384,c_6])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_404,plain,(
    ! [A_1] :
      ( r1_xboole_0(A_1,k2_struct_0('#skF_7'))
      | ~ r1_tarski(A_1,k2_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_2])).

tff(c_52,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_126,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_79])).

tff(c_188,plain,(
    ! [A_88,B_89] :
      ( r1_tsep_1(A_88,B_89)
      | ~ r1_xboole_0(u1_struct_0(A_88),u1_struct_0(B_89))
      | ~ l1_struct_0(B_89)
      | ~ l1_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_206,plain,(
    ! [A_88] :
      ( r1_tsep_1(A_88,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_88),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_188])).

tff(c_522,plain,(
    ! [A_107] :
      ( r1_tsep_1(A_107,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_107),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_206])).

tff(c_528,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_522])).

tff(c_542,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_528])).

tff(c_586,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_589,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_586])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_589])).

tff(c_594,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_607,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_404,c_594])).

tff(c_611,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_607])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_114,c_54,c_611])).

tff(c_617,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_616,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_684,plain,(
    ! [B_124,A_125] :
      ( r1_tsep_1(B_124,A_125)
      | ~ r1_tsep_1(A_125,B_124)
      | ~ l1_struct_0(B_124)
      | ~ l1_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_686,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_616,c_684])).

tff(c_689,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_617,c_686])).

tff(c_690,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_693,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_690])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_693])).

tff(c_698,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_707,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_698])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_707])).

tff(c_712,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_713,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_786,plain,(
    ! [B_140,A_141] :
      ( r1_tsep_1(B_140,A_141)
      | ~ r1_tsep_1(A_141,B_140)
      | ~ l1_struct_0(B_140)
      | ~ l1_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_790,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_713,c_786])).

tff(c_794,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_790])).

tff(c_796,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_794])).

tff(c_799,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_796])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_799])).

tff(c_804,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_794])).

tff(c_808,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_804])).

tff(c_812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.87/1.44  
% 2.87/1.44  %Foreground sorts:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Background operators:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Foreground operators:
% 2.87/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.87/1.44  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.87/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.87/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.87/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.87/1.44  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.87/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.87/1.44  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.87/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.44  
% 2.87/1.46  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 2.87/1.46  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.87/1.46  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.87/1.46  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 2.87/1.46  tff(f_88, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.87/1.46  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.87/1.46  tff(f_80, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.87/1.46  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.87/1.46  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.87/1.46  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.46  tff(c_56, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.46  tff(c_735, plain, (![B_132, A_133]: (l1_pre_topc(B_132) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.46  tff(c_738, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_735])).
% 2.87/1.46  tff(c_750, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_738])).
% 2.87/1.46  tff(c_40, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.46  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.46  tff(c_741, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_735])).
% 2.87/1.46  tff(c_753, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_741])).
% 2.87/1.46  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.46  tff(c_633, plain, (![B_116, A_117]: (l1_pre_topc(B_116) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.46  tff(c_645, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_633])).
% 2.87/1.46  tff(c_655, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_645])).
% 2.87/1.46  tff(c_636, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_633])).
% 2.87/1.46  tff(c_648, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_636])).
% 2.87/1.46  tff(c_96, plain, (![B_74, A_75]: (l1_pre_topc(B_74) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.46  tff(c_108, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_96])).
% 2.87/1.46  tff(c_118, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_108])).
% 2.87/1.46  tff(c_102, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_96])).
% 2.87/1.46  tff(c_114, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102])).
% 2.87/1.46  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.46  tff(c_30, plain, (![B_29, A_7]: (r1_tarski(k2_struct_0(B_29), k2_struct_0(A_7)) | ~m1_pre_topc(B_29, A_7) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.46  tff(c_99, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_96])).
% 2.87/1.46  tff(c_111, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_99])).
% 2.87/1.46  tff(c_50, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.46  tff(c_80, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 2.87/1.46  tff(c_147, plain, (![B_82, A_83]: (r1_tsep_1(B_82, A_83) | ~r1_tsep_1(A_83, B_82) | ~l1_struct_0(B_82) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.87/1.46  tff(c_150, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_80, c_147])).
% 2.87/1.46  tff(c_151, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_150])).
% 2.87/1.46  tff(c_154, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_151])).
% 2.87/1.46  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_154])).
% 2.87/1.46  tff(c_159, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_150])).
% 2.87/1.46  tff(c_166, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_159])).
% 2.87/1.46  tff(c_170, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_166])).
% 2.87/1.46  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_170])).
% 2.87/1.46  tff(c_176, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_159])).
% 2.87/1.46  tff(c_75, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.46  tff(c_79, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_40, c_75])).
% 2.87/1.46  tff(c_122, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_111, c_79])).
% 2.87/1.46  tff(c_160, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_150])).
% 2.87/1.46  tff(c_130, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_118, c_79])).
% 2.87/1.46  tff(c_251, plain, (![A_91, B_92]: (r1_xboole_0(u1_struct_0(A_91), u1_struct_0(B_92)) | ~r1_tsep_1(A_91, B_92) | ~l1_struct_0(B_92) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.87/1.46  tff(c_266, plain, (![B_92]: (r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_92)) | ~r1_tsep_1('#skF_6', B_92) | ~l1_struct_0(B_92) | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_251])).
% 2.87/1.46  tff(c_359, plain, (![B_96]: (r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_96)) | ~r1_tsep_1('#skF_6', B_96) | ~l1_struct_0(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_266])).
% 2.87/1.46  tff(c_374, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7')) | ~r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_122, c_359])).
% 2.87/1.46  tff(c_384, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_80, c_374])).
% 2.87/1.46  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=A_4 | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.46  tff(c_393, plain, (k4_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_384, c_6])).
% 2.87/1.46  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.46  tff(c_404, plain, (![A_1]: (r1_xboole_0(A_1, k2_struct_0('#skF_7')) | ~r1_tarski(A_1, k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_393, c_2])).
% 2.87/1.46  tff(c_52, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.87/1.46  tff(c_74, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 2.87/1.46  tff(c_126, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_114, c_79])).
% 2.87/1.46  tff(c_188, plain, (![A_88, B_89]: (r1_tsep_1(A_88, B_89) | ~r1_xboole_0(u1_struct_0(A_88), u1_struct_0(B_89)) | ~l1_struct_0(B_89) | ~l1_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.87/1.46  tff(c_206, plain, (![A_88]: (r1_tsep_1(A_88, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_88), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_88))), inference(superposition, [status(thm), theory('equality')], [c_122, c_188])).
% 2.87/1.46  tff(c_522, plain, (![A_107]: (r1_tsep_1(A_107, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_107), k2_struct_0('#skF_7')) | ~l1_struct_0(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_206])).
% 2.87/1.46  tff(c_528, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_126, c_522])).
% 2.87/1.46  tff(c_542, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_528])).
% 2.87/1.46  tff(c_586, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_542])).
% 2.87/1.46  tff(c_589, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_586])).
% 2.87/1.46  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_589])).
% 2.87/1.46  tff(c_594, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_542])).
% 2.87/1.46  tff(c_607, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_404, c_594])).
% 2.87/1.46  tff(c_611, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_30, c_607])).
% 2.87/1.46  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_114, c_54, c_611])).
% 2.87/1.46  tff(c_617, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 2.87/1.46  tff(c_616, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 2.87/1.46  tff(c_684, plain, (![B_124, A_125]: (r1_tsep_1(B_124, A_125) | ~r1_tsep_1(A_125, B_124) | ~l1_struct_0(B_124) | ~l1_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.87/1.46  tff(c_686, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_616, c_684])).
% 2.87/1.46  tff(c_689, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_617, c_686])).
% 2.87/1.46  tff(c_690, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_689])).
% 2.87/1.46  tff(c_693, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_690])).
% 2.87/1.46  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_648, c_693])).
% 2.87/1.46  tff(c_698, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_689])).
% 2.87/1.46  tff(c_707, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_698])).
% 2.87/1.46  tff(c_711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_655, c_707])).
% 2.87/1.46  tff(c_712, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.46  tff(c_713, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.46  tff(c_786, plain, (![B_140, A_141]: (r1_tsep_1(B_140, A_141) | ~r1_tsep_1(A_141, B_140) | ~l1_struct_0(B_140) | ~l1_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.87/1.46  tff(c_790, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_713, c_786])).
% 2.87/1.46  tff(c_794, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_712, c_790])).
% 2.87/1.46  tff(c_796, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_794])).
% 2.87/1.46  tff(c_799, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_796])).
% 2.87/1.46  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_753, c_799])).
% 2.87/1.46  tff(c_804, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_794])).
% 2.87/1.46  tff(c_808, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_804])).
% 2.87/1.46  tff(c_812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_750, c_808])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 156
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 16
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 4
% 2.87/1.46  #Demod        : 83
% 2.87/1.46  #Tautology    : 46
% 2.87/1.46  #SimpNegUnit  : 10
% 2.87/1.46  #BackRed      : 0
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.35
% 2.87/1.46  Parsing              : 0.18
% 2.87/1.46  CNF conversion       : 0.03
% 2.87/1.46  Main loop            : 0.34
% 2.87/1.46  Inferencing          : 0.11
% 2.87/1.46  Reduction            : 0.10
% 2.87/1.46  Demodulation         : 0.07
% 2.87/1.46  BG Simplification    : 0.02
% 2.87/1.46  Subsumption          : 0.07
% 2.87/1.46  Abstraction          : 0.02
% 2.87/1.46  MUC search           : 0.00
% 2.87/1.46  Cooper               : 0.00
% 2.87/1.46  Total                : 0.73
% 2.87/1.46  Index Insertion      : 0.00
% 2.87/1.46  Index Deletion       : 0.00
% 2.87/1.46  Index Matching       : 0.00
% 2.87/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
