%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:31 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 545 expanded)
%              Number of leaves         :   38 ( 197 expanded)
%              Depth                    :   14
%              Number of atoms          :  206 (1615 expanded)
%              Number of equality atoms :   10 (  85 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
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

tff(f_116,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_64,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_115,plain,(
    ! [B_75,A_76] :
      ( l1_pre_topc(B_75)
      | ~ m1_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_118,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_127,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_118])).

tff(c_44,plain,(
    ! [A_54] :
      ( l1_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_76,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_135,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_127,c_80])).

tff(c_48,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(u1_struct_0(A_58))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_150,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_48])).

tff(c_153,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_150])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_167])).

tff(c_172,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    m1_pre_topc('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_115])).

tff(c_130,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_121])).

tff(c_58,plain,(
    m1_pre_topc('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    ! [B_36,A_14] :
      ( r1_tarski(k2_struct_0(B_36),k2_struct_0(A_14))
      | ~ m1_pre_topc(B_36,A_14)
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_173,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_139,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_130,c_80])).

tff(c_158,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_48])).

tff(c_161,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_158])).

tff(c_179,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_182,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_182])).

tff(c_188,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_56,plain,
    ( r1_tsep_1('#skF_8','#skF_7')
    | r1_tsep_1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_74,plain,(
    r1_tsep_1('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_215,plain,(
    ! [B_94,A_95] :
      ( r1_tsep_1(B_94,A_95)
      | ~ r1_tsep_1(A_95,B_94)
      | ~ l1_struct_0(B_94)
      | ~ l1_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_217,plain,
    ( r1_tsep_1('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_215])).

tff(c_220,plain,(
    r1_tsep_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_188,c_217])).

tff(c_230,plain,(
    ! [A_98,B_99] :
      ( r1_xboole_0(u1_struct_0(A_98),u1_struct_0(B_99))
      | ~ r1_tsep_1(A_98,B_99)
      | ~ l1_struct_0(B_99)
      | ~ l1_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_237,plain,(
    ! [B_99] :
      ( r1_xboole_0(k2_struct_0('#skF_8'),u1_struct_0(B_99))
      | ~ r1_tsep_1('#skF_8',B_99)
      | ~ l1_struct_0(B_99)
      | ~ l1_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_230])).

tff(c_267,plain,(
    ! [B_100] :
      ( r1_xboole_0(k2_struct_0('#skF_8'),u1_struct_0(B_100))
      | ~ r1_tsep_1('#skF_8',B_100)
      | ~ l1_struct_0(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_237])).

tff(c_277,plain,
    ( r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_7'))
    | ~ r1_tsep_1('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_267])).

tff(c_286,plain,(
    r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_220,c_277])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_xboole_0(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_293,plain,(
    ! [A_10] :
      ( r1_xboole_0(A_10,k2_struct_0('#skF_7'))
      | ~ r1_tarski(A_10,k2_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_286,c_12])).

tff(c_322,plain,(
    ! [A_103,B_104] :
      ( r1_tsep_1(A_103,B_104)
      | ~ r1_xboole_0(u1_struct_0(A_103),u1_struct_0(B_104))
      | ~ l1_struct_0(B_104)
      | ~ l1_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_343,plain,(
    ! [A_103] :
      ( r1_tsep_1(A_103,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_103),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_322])).

tff(c_606,plain,(
    ! [A_120] :
      ( r1_tsep_1(A_120,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_120),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_343])).

tff(c_621,plain,
    ( r1_tsep_1('#skF_7','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_606])).

tff(c_631,plain,
    ( r1_tsep_1('#skF_7','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_621])).

tff(c_650,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_660,plain,(
    ~ r1_tarski(k2_struct_0('#skF_7'),k2_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_293,c_650])).

tff(c_681,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_8')
    | ~ l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_660])).

tff(c_685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_127,c_58,c_681])).

tff(c_687,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_6,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_722,plain,(
    ! [C_126] : ~ r2_hidden(C_126,k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_687,c_6])).

tff(c_734,plain,(
    v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_722])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_734])).

tff(c_742,plain,(
    ~ r1_tsep_1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_763,plain,(
    ! [B_132,A_133] :
      ( l1_pre_topc(B_132)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_769,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_763])).

tff(c_778,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_769])).

tff(c_749,plain,(
    ! [A_130] :
      ( u1_struct_0(A_130) = k2_struct_0(A_130)
      | ~ l1_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_753,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_44,c_749])).

tff(c_787,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_778,c_753])).

tff(c_798,plain,(
    ! [A_134] :
      ( ~ v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_801,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_798])).

tff(c_808,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_801])).

tff(c_811,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_808])).

tff(c_814,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_811])).

tff(c_818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_814])).

tff(c_820,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_808])).

tff(c_766,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_763])).

tff(c_775,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_766])).

tff(c_783,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_775,c_753])).

tff(c_804,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_798])).

tff(c_809,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_804])).

tff(c_826,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_809])).

tff(c_829,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_826])).

tff(c_833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_829])).

tff(c_835,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_741,plain,(
    r1_tsep_1('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_888,plain,(
    ! [B_154,A_155] :
      ( r1_tsep_1(B_154,A_155)
      | ~ r1_tsep_1(A_155,B_154)
      | ~ l1_struct_0(B_154)
      | ~ l1_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_890,plain,
    ( r1_tsep_1('#skF_7','#skF_8')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_741,c_888])).

tff(c_893,plain,(
    r1_tsep_1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_835,c_890])).

tff(c_895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.56  
% 3.21/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.56  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 3.21/1.56  
% 3.21/1.56  %Foreground sorts:
% 3.21/1.56  
% 3.21/1.56  
% 3.21/1.56  %Background operators:
% 3.21/1.56  
% 3.21/1.56  
% 3.21/1.56  %Foreground operators:
% 3.21/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.56  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.21/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.21/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.21/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.21/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.21/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.21/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.21/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.21/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.21/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.56  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.21/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.21/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.21/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.21/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.21/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.56  
% 3.21/1.58  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 3.21/1.58  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.21/1.58  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.21/1.58  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.21/1.58  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.21/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.21/1.58  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.21/1.58  tff(f_116, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.21/1.58  tff(f_108, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.21/1.58  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.21/1.58  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.21/1.58  tff(c_68, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.21/1.58  tff(c_64, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.21/1.58  tff(c_115, plain, (![B_75, A_76]: (l1_pre_topc(B_75) | ~m1_pre_topc(B_75, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.58  tff(c_118, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_115])).
% 3.21/1.58  tff(c_127, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_118])).
% 3.21/1.58  tff(c_44, plain, (![A_54]: (l1_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.58  tff(c_66, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.21/1.58  tff(c_76, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.21/1.58  tff(c_80, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_44, c_76])).
% 3.21/1.58  tff(c_135, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_127, c_80])).
% 3.21/1.58  tff(c_48, plain, (![A_58]: (~v1_xboole_0(u1_struct_0(A_58)) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.21/1.58  tff(c_150, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_135, c_48])).
% 3.21/1.58  tff(c_153, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_66, c_150])).
% 3.21/1.58  tff(c_164, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_153])).
% 3.21/1.58  tff(c_167, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_44, c_164])).
% 3.21/1.58  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_167])).
% 3.21/1.58  tff(c_172, plain, (~v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_153])).
% 3.21/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.58  tff(c_60, plain, (m1_pre_topc('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.21/1.58  tff(c_121, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_60, c_115])).
% 3.21/1.58  tff(c_130, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_121])).
% 3.21/1.58  tff(c_58, plain, (m1_pre_topc('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.21/1.58  tff(c_34, plain, (![B_36, A_14]: (r1_tarski(k2_struct_0(B_36), k2_struct_0(A_14)) | ~m1_pre_topc(B_36, A_14) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.58  tff(c_173, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_153])).
% 3.21/1.58  tff(c_62, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.21/1.58  tff(c_139, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_130, c_80])).
% 3.21/1.58  tff(c_158, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_139, c_48])).
% 3.21/1.58  tff(c_161, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_158])).
% 3.21/1.58  tff(c_179, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_161])).
% 3.21/1.58  tff(c_182, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_44, c_179])).
% 3.21/1.58  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_182])).
% 3.21/1.58  tff(c_188, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_161])).
% 3.21/1.58  tff(c_56, plain, (r1_tsep_1('#skF_8', '#skF_7') | r1_tsep_1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.21/1.58  tff(c_74, plain, (r1_tsep_1('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_56])).
% 3.21/1.58  tff(c_215, plain, (![B_94, A_95]: (r1_tsep_1(B_94, A_95) | ~r1_tsep_1(A_95, B_94) | ~l1_struct_0(B_94) | ~l1_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.21/1.58  tff(c_217, plain, (r1_tsep_1('#skF_8', '#skF_7') | ~l1_struct_0('#skF_8') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_74, c_215])).
% 3.21/1.58  tff(c_220, plain, (r1_tsep_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_188, c_217])).
% 3.21/1.58  tff(c_230, plain, (![A_98, B_99]: (r1_xboole_0(u1_struct_0(A_98), u1_struct_0(B_99)) | ~r1_tsep_1(A_98, B_99) | ~l1_struct_0(B_99) | ~l1_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.21/1.58  tff(c_237, plain, (![B_99]: (r1_xboole_0(k2_struct_0('#skF_8'), u1_struct_0(B_99)) | ~r1_tsep_1('#skF_8', B_99) | ~l1_struct_0(B_99) | ~l1_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_230])).
% 3.21/1.58  tff(c_267, plain, (![B_100]: (r1_xboole_0(k2_struct_0('#skF_8'), u1_struct_0(B_100)) | ~r1_tsep_1('#skF_8', B_100) | ~l1_struct_0(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_237])).
% 3.21/1.58  tff(c_277, plain, (r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_7')) | ~r1_tsep_1('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_135, c_267])).
% 3.21/1.58  tff(c_286, plain, (r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_220, c_277])).
% 3.21/1.58  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_xboole_0(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.58  tff(c_293, plain, (![A_10]: (r1_xboole_0(A_10, k2_struct_0('#skF_7')) | ~r1_tarski(A_10, k2_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_286, c_12])).
% 3.21/1.58  tff(c_322, plain, (![A_103, B_104]: (r1_tsep_1(A_103, B_104) | ~r1_xboole_0(u1_struct_0(A_103), u1_struct_0(B_104)) | ~l1_struct_0(B_104) | ~l1_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.21/1.58  tff(c_343, plain, (![A_103]: (r1_tsep_1(A_103, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_103), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_103))), inference(superposition, [status(thm), theory('equality')], [c_135, c_322])).
% 3.21/1.58  tff(c_606, plain, (![A_120]: (r1_tsep_1(A_120, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_120), k2_struct_0('#skF_7')) | ~l1_struct_0(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_343])).
% 3.21/1.58  tff(c_621, plain, (r1_tsep_1('#skF_7', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_135, c_606])).
% 3.21/1.58  tff(c_631, plain, (r1_tsep_1('#skF_7', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_621])).
% 3.21/1.58  tff(c_650, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_631])).
% 3.21/1.58  tff(c_660, plain, (~r1_tarski(k2_struct_0('#skF_7'), k2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_293, c_650])).
% 3.21/1.58  tff(c_681, plain, (~m1_pre_topc('#skF_7', '#skF_8') | ~l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_34, c_660])).
% 3.21/1.58  tff(c_685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_127, c_58, c_681])).
% 3.21/1.58  tff(c_687, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_631])).
% 3.21/1.58  tff(c_6, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.58  tff(c_722, plain, (![C_126]: (~r2_hidden(C_126, k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_687, c_6])).
% 3.21/1.58  tff(c_734, plain, (v1_xboole_0(k2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_722])).
% 3.21/1.58  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_734])).
% 3.21/1.58  tff(c_742, plain, (~r1_tsep_1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 3.21/1.58  tff(c_763, plain, (![B_132, A_133]: (l1_pre_topc(B_132) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.58  tff(c_769, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_60, c_763])).
% 3.21/1.58  tff(c_778, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_769])).
% 3.21/1.58  tff(c_749, plain, (![A_130]: (u1_struct_0(A_130)=k2_struct_0(A_130) | ~l1_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.21/1.58  tff(c_753, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_44, c_749])).
% 3.21/1.58  tff(c_787, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_778, c_753])).
% 3.21/1.58  tff(c_798, plain, (![A_134]: (~v1_xboole_0(u1_struct_0(A_134)) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.21/1.58  tff(c_801, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_787, c_798])).
% 3.21/1.58  tff(c_808, plain, (~v1_xboole_0(k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_801])).
% 3.21/1.58  tff(c_811, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_808])).
% 3.21/1.58  tff(c_814, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_44, c_811])).
% 3.21/1.58  tff(c_818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_778, c_814])).
% 3.21/1.58  tff(c_820, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_808])).
% 3.21/1.58  tff(c_766, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_763])).
% 3.21/1.58  tff(c_775, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_766])).
% 3.21/1.58  tff(c_783, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_775, c_753])).
% 3.21/1.58  tff(c_804, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_783, c_798])).
% 3.21/1.58  tff(c_809, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_66, c_804])).
% 3.21/1.58  tff(c_826, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_809])).
% 3.21/1.58  tff(c_829, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_44, c_826])).
% 3.21/1.58  tff(c_833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_775, c_829])).
% 3.21/1.58  tff(c_835, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_809])).
% 3.21/1.58  tff(c_741, plain, (r1_tsep_1('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 3.21/1.58  tff(c_888, plain, (![B_154, A_155]: (r1_tsep_1(B_154, A_155) | ~r1_tsep_1(A_155, B_154) | ~l1_struct_0(B_154) | ~l1_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.21/1.58  tff(c_890, plain, (r1_tsep_1('#skF_7', '#skF_8') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_741, c_888])).
% 3.21/1.58  tff(c_893, plain, (r1_tsep_1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_835, c_890])).
% 3.21/1.58  tff(c_895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_742, c_893])).
% 3.21/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.58  
% 3.21/1.58  Inference rules
% 3.21/1.58  ----------------------
% 3.21/1.58  #Ref     : 0
% 3.21/1.58  #Sup     : 170
% 3.21/1.58  #Fact    : 0
% 3.21/1.58  #Define  : 0
% 3.21/1.58  #Split   : 13
% 3.21/1.58  #Chain   : 0
% 3.21/1.58  #Close   : 0
% 3.21/1.58  
% 3.21/1.58  Ordering : KBO
% 3.21/1.58  
% 3.21/1.58  Simplification rules
% 3.21/1.58  ----------------------
% 3.21/1.58  #Subsume      : 40
% 3.21/1.58  #Demod        : 97
% 3.21/1.58  #Tautology    : 29
% 3.21/1.58  #SimpNegUnit  : 16
% 3.21/1.58  #BackRed      : 0
% 3.21/1.58  
% 3.21/1.58  #Partial instantiations: 0
% 3.21/1.58  #Strategies tried      : 1
% 3.21/1.58  
% 3.21/1.58  Timing (in seconds)
% 3.21/1.58  ----------------------
% 3.21/1.59  Preprocessing        : 0.36
% 3.21/1.59  Parsing              : 0.18
% 3.21/1.59  CNF conversion       : 0.03
% 3.21/1.59  Main loop            : 0.36
% 3.21/1.59  Inferencing          : 0.12
% 3.21/1.59  Reduction            : 0.11
% 3.21/1.59  Demodulation         : 0.07
% 3.21/1.59  BG Simplification    : 0.02
% 3.21/1.59  Subsumption          : 0.07
% 3.21/1.59  Abstraction          : 0.02
% 3.21/1.59  MUC search           : 0.00
% 3.21/1.59  Cooper               : 0.00
% 3.21/1.59  Total                : 0.76
% 3.21/1.59  Index Insertion      : 0.00
% 3.21/1.59  Index Deletion       : 0.00
% 3.21/1.59  Index Matching       : 0.00
% 3.21/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
