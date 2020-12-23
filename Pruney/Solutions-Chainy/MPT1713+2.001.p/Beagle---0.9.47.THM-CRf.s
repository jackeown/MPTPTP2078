%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:29 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 183 expanded)
%              Number of leaves         :   32 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 ( 582 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_395,plain,(
    ! [B_110,A_111] :
      ( l1_pre_topc(B_110)
      | ~ m1_pre_topc(B_110,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_398,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_395])).

tff(c_407,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_398])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_401,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_395])).

tff(c_410,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_401])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    ! [B_46,A_47] :
      ( l1_pre_topc(B_46)
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_80,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_71])).

tff(c_36,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_55,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_119,plain,(
    ! [B_57,A_58] :
      ( r1_tsep_1(B_57,A_58)
      | ~ r1_tsep_1(A_58,B_57)
      | ~ l1_struct_0(B_57)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_122,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_119])).

tff(c_125,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_128,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_128])).

tff(c_134,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_83,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_74])).

tff(c_133,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_135,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_138,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_138])).

tff(c_144,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_100,plain,(
    ! [B_55,A_56] :
      ( v2_pre_topc(B_55)
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_115,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_106])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_204,plain,(
    ! [B_86,C_87,A_88] :
      ( m1_pre_topc(B_86,C_87)
      | ~ r1_tarski(u1_struct_0(B_86),u1_struct_0(C_87))
      | ~ m1_pre_topc(C_87,A_88)
      | ~ m1_pre_topc(B_86,A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_209,plain,(
    ! [B_89,A_90] :
      ( m1_pre_topc(B_89,B_89)
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_213,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_209])).

tff(c_221,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_213])).

tff(c_260,plain,(
    ! [B_91,C_92,A_93] :
      ( r1_tarski(u1_struct_0(B_91),u1_struct_0(C_92))
      | ~ m1_pre_topc(B_91,C_92)
      | ~ m1_pre_topc(C_92,A_93)
      | ~ m1_pre_topc(B_91,A_93)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_262,plain,(
    ! [B_91] :
      ( r1_tarski(u1_struct_0(B_91),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_91,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_221,c_260])).

tff(c_286,plain,(
    ! [B_94] :
      ( r1_tarski(u1_struct_0(B_94),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_94,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_83,c_262])).

tff(c_162,plain,(
    ! [A_67,B_68] :
      ( r1_xboole_0(u1_struct_0(A_67),u1_struct_0(B_68))
      | ~ r1_tsep_1(A_67,B_68)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,k2_xboole_0(C_9,B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,B_60)
      | ~ r1_xboole_0(A_59,C_61)
      | ~ r1_tarski(A_59,k2_xboole_0(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_xboole_0(A_7,B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_165,plain,(
    ! [A_67,C_9,B_68] :
      ( r1_tarski(u1_struct_0(A_67),C_9)
      | ~ r1_tarski(u1_struct_0(A_67),u1_struct_0(B_68))
      | ~ r1_tsep_1(A_67,B_68)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_162,c_158])).

tff(c_290,plain,(
    ! [B_94,C_9] :
      ( r1_tarski(u1_struct_0(B_94),C_9)
      | ~ r1_tsep_1(B_94,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(B_94)
      | ~ m1_pre_topc(B_94,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_286,c_165])).

tff(c_345,plain,(
    ! [B_100,C_101] :
      ( r1_tarski(u1_struct_0(B_100),C_101)
      | ~ r1_tsep_1(B_100,'#skF_4')
      | ~ l1_struct_0(B_100)
      | ~ m1_pre_topc(B_100,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_290])).

tff(c_59,plain,(
    ! [A_45] :
      ( v1_xboole_0(A_45)
      | r2_hidden('#skF_1'(A_45),A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [A_45] :
      ( ~ r1_tarski(A_45,'#skF_1'(A_45))
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_59,c_16])).

tff(c_367,plain,(
    ! [B_102] :
      ( v1_xboole_0(u1_struct_0(B_102))
      | ~ r1_tsep_1(B_102,'#skF_4')
      | ~ l1_struct_0(B_102)
      | ~ m1_pre_topc(B_102,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_345,c_66])).

tff(c_24,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_372,plain,(
    ! [B_103] :
      ( v2_struct_0(B_103)
      | ~ r1_tsep_1(B_103,'#skF_4')
      | ~ l1_struct_0(B_103)
      | ~ m1_pre_topc(B_103,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_367,c_24])).

tff(c_375,plain,
    ( v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_55,c_372])).

tff(c_378,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_134,c_375])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_378])).

tff(c_382,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_381,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_448,plain,(
    ! [B_121,A_122] :
      ( r1_tsep_1(B_121,A_122)
      | ~ r1_tsep_1(A_122,B_121)
      | ~ l1_struct_0(B_121)
      | ~ l1_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_450,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_381,c_448])).

tff(c_453,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_450])).

tff(c_454,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_453])).

tff(c_457,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_454])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_457])).

tff(c_462,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_466,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_462])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.51  
% 2.65/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.52  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.65/1.52  
% 2.65/1.52  %Foreground sorts:
% 2.65/1.52  
% 2.65/1.52  
% 2.65/1.52  %Background operators:
% 2.65/1.52  
% 2.65/1.52  
% 2.65/1.52  %Foreground operators:
% 2.65/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.65/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.65/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.65/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.52  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.65/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.52  
% 2.73/1.53  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.73/1.53  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.73/1.53  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.73/1.53  tff(f_97, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.73/1.53  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.73/1.53  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.53  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.73/1.53  tff(f_89, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.73/1.53  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.73/1.53  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.73/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.73/1.53  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.73/1.53  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.73/1.53  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.73/1.53  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.73/1.53  tff(c_395, plain, (![B_110, A_111]: (l1_pre_topc(B_110) | ~m1_pre_topc(B_110, A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.73/1.53  tff(c_398, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_395])).
% 2.73/1.53  tff(c_407, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_398])).
% 2.73/1.53  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.53  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.73/1.53  tff(c_401, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_395])).
% 2.73/1.53  tff(c_410, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_401])).
% 2.73/1.53  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.73/1.53  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.73/1.53  tff(c_68, plain, (![B_46, A_47]: (l1_pre_topc(B_46) | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.73/1.53  tff(c_71, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_68])).
% 2.73/1.53  tff(c_80, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_71])).
% 2.73/1.53  tff(c_36, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.73/1.53  tff(c_55, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 2.73/1.53  tff(c_119, plain, (![B_57, A_58]: (r1_tsep_1(B_57, A_58) | ~r1_tsep_1(A_58, B_57) | ~l1_struct_0(B_57) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.53  tff(c_122, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_55, c_119])).
% 2.73/1.53  tff(c_125, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_122])).
% 2.73/1.53  tff(c_128, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_125])).
% 2.73/1.53  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_128])).
% 2.73/1.53  tff(c_134, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_122])).
% 2.73/1.53  tff(c_74, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_68])).
% 2.73/1.53  tff(c_83, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_74])).
% 2.73/1.53  tff(c_133, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_122])).
% 2.73/1.53  tff(c_135, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_133])).
% 2.73/1.53  tff(c_138, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_135])).
% 2.73/1.53  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_138])).
% 2.73/1.53  tff(c_144, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_133])).
% 2.73/1.53  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.73/1.53  tff(c_100, plain, (![B_55, A_56]: (v2_pre_topc(B_55) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.53  tff(c_106, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_100])).
% 2.73/1.53  tff(c_115, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_106])).
% 2.73/1.53  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.53  tff(c_204, plain, (![B_86, C_87, A_88]: (m1_pre_topc(B_86, C_87) | ~r1_tarski(u1_struct_0(B_86), u1_struct_0(C_87)) | ~m1_pre_topc(C_87, A_88) | ~m1_pre_topc(B_86, A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.53  tff(c_209, plain, (![B_89, A_90]: (m1_pre_topc(B_89, B_89) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(resolution, [status(thm)], [c_10, c_204])).
% 2.73/1.53  tff(c_213, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_209])).
% 2.73/1.53  tff(c_221, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_213])).
% 2.73/1.53  tff(c_260, plain, (![B_91, C_92, A_93]: (r1_tarski(u1_struct_0(B_91), u1_struct_0(C_92)) | ~m1_pre_topc(B_91, C_92) | ~m1_pre_topc(C_92, A_93) | ~m1_pre_topc(B_91, A_93) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.53  tff(c_262, plain, (![B_91]: (r1_tarski(u1_struct_0(B_91), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_91, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_221, c_260])).
% 2.73/1.53  tff(c_286, plain, (![B_94]: (r1_tarski(u1_struct_0(B_94), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_94, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_83, c_262])).
% 2.73/1.53  tff(c_162, plain, (![A_67, B_68]: (r1_xboole_0(u1_struct_0(A_67), u1_struct_0(B_68)) | ~r1_tsep_1(A_67, B_68) | ~l1_struct_0(B_68) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.73/1.53  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, k2_xboole_0(C_9, B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.54  tff(c_150, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, B_60) | ~r1_xboole_0(A_59, C_61) | ~r1_tarski(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.54  tff(c_158, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_xboole_0(A_7, B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_150])).
% 2.73/1.54  tff(c_165, plain, (![A_67, C_9, B_68]: (r1_tarski(u1_struct_0(A_67), C_9) | ~r1_tarski(u1_struct_0(A_67), u1_struct_0(B_68)) | ~r1_tsep_1(A_67, B_68) | ~l1_struct_0(B_68) | ~l1_struct_0(A_67))), inference(resolution, [status(thm)], [c_162, c_158])).
% 2.73/1.54  tff(c_290, plain, (![B_94, C_9]: (r1_tarski(u1_struct_0(B_94), C_9) | ~r1_tsep_1(B_94, '#skF_4') | ~l1_struct_0('#skF_4') | ~l1_struct_0(B_94) | ~m1_pre_topc(B_94, '#skF_4'))), inference(resolution, [status(thm)], [c_286, c_165])).
% 2.73/1.54  tff(c_345, plain, (![B_100, C_101]: (r1_tarski(u1_struct_0(B_100), C_101) | ~r1_tsep_1(B_100, '#skF_4') | ~l1_struct_0(B_100) | ~m1_pre_topc(B_100, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_290])).
% 2.73/1.54  tff(c_59, plain, (![A_45]: (v1_xboole_0(A_45) | r2_hidden('#skF_1'(A_45), A_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.54  tff(c_16, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.54  tff(c_66, plain, (![A_45]: (~r1_tarski(A_45, '#skF_1'(A_45)) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_59, c_16])).
% 2.73/1.54  tff(c_367, plain, (![B_102]: (v1_xboole_0(u1_struct_0(B_102)) | ~r1_tsep_1(B_102, '#skF_4') | ~l1_struct_0(B_102) | ~m1_pre_topc(B_102, '#skF_4'))), inference(resolution, [status(thm)], [c_345, c_66])).
% 2.73/1.54  tff(c_24, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.54  tff(c_372, plain, (![B_103]: (v2_struct_0(B_103) | ~r1_tsep_1(B_103, '#skF_4') | ~l1_struct_0(B_103) | ~m1_pre_topc(B_103, '#skF_4'))), inference(resolution, [status(thm)], [c_367, c_24])).
% 2.73/1.54  tff(c_375, plain, (v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_55, c_372])).
% 2.73/1.54  tff(c_378, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_134, c_375])).
% 2.73/1.54  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_378])).
% 2.73/1.54  tff(c_382, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.73/1.54  tff(c_381, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.73/1.54  tff(c_448, plain, (![B_121, A_122]: (r1_tsep_1(B_121, A_122) | ~r1_tsep_1(A_122, B_121) | ~l1_struct_0(B_121) | ~l1_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.54  tff(c_450, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_381, c_448])).
% 2.73/1.54  tff(c_453, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_382, c_450])).
% 2.73/1.54  tff(c_454, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_453])).
% 2.73/1.54  tff(c_457, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_454])).
% 2.73/1.54  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_410, c_457])).
% 2.73/1.54  tff(c_462, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_453])).
% 2.73/1.54  tff(c_466, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_462])).
% 2.73/1.54  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_407, c_466])).
% 2.73/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.54  
% 2.73/1.54  Inference rules
% 2.73/1.54  ----------------------
% 2.73/1.54  #Ref     : 0
% 2.73/1.54  #Sup     : 72
% 2.73/1.54  #Fact    : 0
% 2.73/1.54  #Define  : 0
% 2.73/1.54  #Split   : 4
% 2.73/1.54  #Chain   : 0
% 2.73/1.54  #Close   : 0
% 2.73/1.54  
% 2.73/1.54  Ordering : KBO
% 2.73/1.54  
% 2.73/1.54  Simplification rules
% 2.73/1.54  ----------------------
% 2.73/1.54  #Subsume      : 7
% 2.73/1.54  #Demod        : 70
% 2.73/1.54  #Tautology    : 21
% 2.73/1.54  #SimpNegUnit  : 3
% 2.73/1.54  #BackRed      : 0
% 2.73/1.54  
% 2.73/1.54  #Partial instantiations: 0
% 2.73/1.54  #Strategies tried      : 1
% 2.73/1.54  
% 2.73/1.54  Timing (in seconds)
% 2.73/1.54  ----------------------
% 2.73/1.54  Preprocessing        : 0.34
% 2.73/1.54  Parsing              : 0.20
% 2.73/1.54  CNF conversion       : 0.02
% 2.73/1.54  Main loop            : 0.28
% 2.73/1.54  Inferencing          : 0.11
% 2.73/1.54  Reduction            : 0.07
% 2.73/1.54  Demodulation         : 0.05
% 2.73/1.54  BG Simplification    : 0.02
% 2.73/1.54  Subsumption          : 0.06
% 2.73/1.54  Abstraction          : 0.01
% 2.73/1.54  MUC search           : 0.00
% 2.73/1.54  Cooper               : 0.00
% 2.73/1.54  Total                : 0.66
% 2.73/1.54  Index Insertion      : 0.00
% 2.73/1.54  Index Deletion       : 0.00
% 2.73/1.54  Index Matching       : 0.00
% 2.73/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
