%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:36 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 299 expanded)
%              Number of leaves         :   28 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  202 (1117 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_327,plain,(
    ! [B_96,A_97] :
      ( l1_pre_topc(B_96)
      | ~ m1_pre_topc(B_96,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_339,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_327])).

tff(c_349,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_339])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_330,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_327])).

tff(c_342,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_330])).

tff(c_260,plain,(
    ! [B_79,A_80] :
      ( l1_pre_topc(B_79)
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_263,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_260])).

tff(c_275,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_263])).

tff(c_40,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_266,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_260])).

tff(c_278,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_266])).

tff(c_28,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_51,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_54,plain,(
    ! [B_36,A_37] :
      ( l1_pre_topc(B_36)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_69,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_57])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_66])).

tff(c_26,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_50,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_91,plain,(
    ! [B_46,A_47] :
      ( r1_tsep_1(B_46,A_47)
      | ~ r1_tsep_1(A_47,B_46)
      | ~ l1_struct_0(B_46)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_91])).

tff(c_95,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_98,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_95])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_98])).

tff(c_103,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_117,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_117])).

tff(c_123,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_122,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_60])).

tff(c_104,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( r1_xboole_0(u1_struct_0(A_12),u1_struct_0(B_14))
      | ~ r1_tsep_1(A_12,B_14)
      | ~ l1_struct_0(B_14)
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_138,plain,(
    ! [B_54,A_55] :
      ( m1_subset_1(u1_struct_0(B_54),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_pre_topc(B_54,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(u1_struct_0(B_56),u1_struct_0(A_57))
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_138,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [B_62,A_63] :
      ( k2_xboole_0(u1_struct_0(B_62),u1_struct_0(A_63)) = u1_struct_0(A_63)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_172,plain,(
    ! [A_64,B_65,A_66] :
      ( r1_xboole_0(A_64,u1_struct_0(B_65))
      | ~ r1_xboole_0(A_64,u1_struct_0(A_66))
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_8])).

tff(c_176,plain,(
    ! [A_67,B_68,B_69] :
      ( r1_xboole_0(u1_struct_0(A_67),u1_struct_0(B_68))
      | ~ m1_pre_topc(B_68,B_69)
      | ~ l1_pre_topc(B_69)
      | ~ r1_tsep_1(A_67,B_69)
      | ~ l1_struct_0(B_69)
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_20,c_172])).

tff(c_182,plain,(
    ! [A_67] :
      ( r1_xboole_0(u1_struct_0(A_67),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tsep_1(A_67,'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_30,c_176])).

tff(c_197,plain,(
    ! [A_70] :
      ( r1_xboole_0(u1_struct_0(A_70),u1_struct_0('#skF_2'))
      | ~ r1_tsep_1(A_70,'#skF_3')
      | ~ l1_struct_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_76,c_182])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( r1_tsep_1(A_12,B_14)
      | ~ r1_xboole_0(u1_struct_0(A_12),u1_struct_0(B_14))
      | ~ l1_struct_0(B_14)
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_206,plain,(
    ! [A_70] :
      ( r1_tsep_1(A_70,'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | ~ r1_tsep_1(A_70,'#skF_3')
      | ~ l1_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_197,c_18])).

tff(c_207,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_220,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_207])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_220])).

tff(c_226,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_227,plain,(
    ! [A_71] :
      ( r1_tsep_1(A_71,'#skF_2')
      | ~ r1_tsep_1(A_71,'#skF_3')
      | ~ l1_struct_0(A_71) ) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tsep_1(B_16,A_15)
      | ~ r1_tsep_1(A_15,B_16)
      | ~ l1_struct_0(B_16)
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_229,plain,(
    ! [A_71] :
      ( r1_tsep_1('#skF_2',A_71)
      | ~ l1_struct_0('#skF_2')
      | ~ r1_tsep_1(A_71,'#skF_3')
      | ~ l1_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_227,c_22])).

tff(c_243,plain,(
    ! [A_72] :
      ( r1_tsep_1('#skF_2',A_72)
      | ~ r1_tsep_1(A_72,'#skF_3')
      | ~ l1_struct_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_229])).

tff(c_245,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_243])).

tff(c_248,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_245])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_248])).

tff(c_251,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_252,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_287,plain,(
    ! [B_87,A_88] :
      ( r1_tsep_1(B_87,A_88)
      | ~ r1_tsep_1(A_88,B_87)
      | ~ l1_struct_0(B_87)
      | ~ l1_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_289,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_252,c_287])).

tff(c_294,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_289])).

tff(c_296,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_299,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_296])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_299])).

tff(c_304,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_317,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_304])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_317])).

tff(c_323,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_322,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_359,plain,(
    ! [B_106,A_107] :
      ( r1_tsep_1(B_106,A_107)
      | ~ r1_tsep_1(A_107,B_106)
      | ~ l1_struct_0(B_106)
      | ~ l1_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_361,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_322,c_359])).

tff(c_364,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_361])).

tff(c_365,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_368,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_365])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_368])).

tff(c_373,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_377,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_373])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  
% 2.32/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.31  
% 2.32/1.31  %Foreground sorts:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Background operators:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Foreground operators:
% 2.32/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.32/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.32/1.31  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.32/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.31  
% 2.61/1.33  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 2.61/1.33  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.61/1.33  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.61/1.33  tff(f_77, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.61/1.33  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.61/1.33  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.61/1.33  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.33  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.61/1.33  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.61/1.33  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.61/1.33  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.61/1.33  tff(c_327, plain, (![B_96, A_97]: (l1_pre_topc(B_96) | ~m1_pre_topc(B_96, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.33  tff(c_339, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_327])).
% 2.61/1.33  tff(c_349, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_339])).
% 2.61/1.33  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.33  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.61/1.33  tff(c_330, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_327])).
% 2.61/1.33  tff(c_342, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_330])).
% 2.61/1.33  tff(c_260, plain, (![B_79, A_80]: (l1_pre_topc(B_79) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.33  tff(c_263, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_260])).
% 2.61/1.33  tff(c_275, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_263])).
% 2.61/1.33  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.61/1.33  tff(c_266, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_260])).
% 2.61/1.33  tff(c_278, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_266])).
% 2.61/1.33  tff(c_28, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.61/1.33  tff(c_51, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.61/1.33  tff(c_54, plain, (![B_36, A_37]: (l1_pre_topc(B_36) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.33  tff(c_57, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_54])).
% 2.61/1.33  tff(c_69, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_57])).
% 2.61/1.33  tff(c_66, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_54])).
% 2.61/1.33  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_66])).
% 2.61/1.33  tff(c_26, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.61/1.33  tff(c_50, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.61/1.33  tff(c_91, plain, (![B_46, A_47]: (r1_tsep_1(B_46, A_47) | ~r1_tsep_1(A_47, B_46) | ~l1_struct_0(B_46) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.33  tff(c_94, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_91])).
% 2.61/1.33  tff(c_95, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 2.61/1.33  tff(c_98, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_95])).
% 2.61/1.33  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_98])).
% 2.61/1.33  tff(c_103, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 2.61/1.33  tff(c_105, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_103])).
% 2.61/1.33  tff(c_117, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_105])).
% 2.61/1.33  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_117])).
% 2.61/1.33  tff(c_123, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_103])).
% 2.61/1.33  tff(c_122, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 2.61/1.33  tff(c_60, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_54])).
% 2.61/1.33  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_60])).
% 2.61/1.33  tff(c_104, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 2.61/1.33  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.61/1.33  tff(c_20, plain, (![A_12, B_14]: (r1_xboole_0(u1_struct_0(A_12), u1_struct_0(B_14)) | ~r1_tsep_1(A_12, B_14) | ~l1_struct_0(B_14) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.33  tff(c_138, plain, (![B_54, A_55]: (m1_subset_1(u1_struct_0(B_54), k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_pre_topc(B_54, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.61/1.33  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.33  tff(c_143, plain, (![B_56, A_57]: (r1_tarski(u1_struct_0(B_56), u1_struct_0(A_57)) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_138, c_10])).
% 2.61/1.33  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.33  tff(c_154, plain, (![B_62, A_63]: (k2_xboole_0(u1_struct_0(B_62), u1_struct_0(A_63))=u1_struct_0(A_63) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_143, c_2])).
% 2.61/1.33  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.33  tff(c_172, plain, (![A_64, B_65, A_66]: (r1_xboole_0(A_64, u1_struct_0(B_65)) | ~r1_xboole_0(A_64, u1_struct_0(A_66)) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_154, c_8])).
% 2.61/1.33  tff(c_176, plain, (![A_67, B_68, B_69]: (r1_xboole_0(u1_struct_0(A_67), u1_struct_0(B_68)) | ~m1_pre_topc(B_68, B_69) | ~l1_pre_topc(B_69) | ~r1_tsep_1(A_67, B_69) | ~l1_struct_0(B_69) | ~l1_struct_0(A_67))), inference(resolution, [status(thm)], [c_20, c_172])).
% 2.61/1.33  tff(c_182, plain, (![A_67]: (r1_xboole_0(u1_struct_0(A_67), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_3') | ~r1_tsep_1(A_67, '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0(A_67))), inference(resolution, [status(thm)], [c_30, c_176])).
% 2.61/1.33  tff(c_197, plain, (![A_70]: (r1_xboole_0(u1_struct_0(A_70), u1_struct_0('#skF_2')) | ~r1_tsep_1(A_70, '#skF_3') | ~l1_struct_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_76, c_182])).
% 2.61/1.33  tff(c_18, plain, (![A_12, B_14]: (r1_tsep_1(A_12, B_14) | ~r1_xboole_0(u1_struct_0(A_12), u1_struct_0(B_14)) | ~l1_struct_0(B_14) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.33  tff(c_206, plain, (![A_70]: (r1_tsep_1(A_70, '#skF_2') | ~l1_struct_0('#skF_2') | ~r1_tsep_1(A_70, '#skF_3') | ~l1_struct_0(A_70))), inference(resolution, [status(thm)], [c_197, c_18])).
% 2.61/1.33  tff(c_207, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_206])).
% 2.61/1.33  tff(c_220, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_207])).
% 2.61/1.33  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_220])).
% 2.61/1.33  tff(c_226, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_206])).
% 2.61/1.33  tff(c_227, plain, (![A_71]: (r1_tsep_1(A_71, '#skF_2') | ~r1_tsep_1(A_71, '#skF_3') | ~l1_struct_0(A_71))), inference(splitRight, [status(thm)], [c_206])).
% 2.61/1.33  tff(c_22, plain, (![B_16, A_15]: (r1_tsep_1(B_16, A_15) | ~r1_tsep_1(A_15, B_16) | ~l1_struct_0(B_16) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.33  tff(c_229, plain, (![A_71]: (r1_tsep_1('#skF_2', A_71) | ~l1_struct_0('#skF_2') | ~r1_tsep_1(A_71, '#skF_3') | ~l1_struct_0(A_71))), inference(resolution, [status(thm)], [c_227, c_22])).
% 2.61/1.33  tff(c_243, plain, (![A_72]: (r1_tsep_1('#skF_2', A_72) | ~r1_tsep_1(A_72, '#skF_3') | ~l1_struct_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_229])).
% 2.61/1.33  tff(c_245, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_122, c_243])).
% 2.61/1.33  tff(c_248, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_245])).
% 2.61/1.33  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_248])).
% 2.61/1.33  tff(c_251, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.61/1.33  tff(c_252, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.61/1.33  tff(c_287, plain, (![B_87, A_88]: (r1_tsep_1(B_87, A_88) | ~r1_tsep_1(A_88, B_87) | ~l1_struct_0(B_87) | ~l1_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.33  tff(c_289, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_252, c_287])).
% 2.61/1.33  tff(c_294, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_251, c_289])).
% 2.61/1.33  tff(c_296, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_294])).
% 2.61/1.33  tff(c_299, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_296])).
% 2.61/1.33  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_299])).
% 2.61/1.33  tff(c_304, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_294])).
% 2.61/1.33  tff(c_317, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_304])).
% 2.61/1.33  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_275, c_317])).
% 2.61/1.33  tff(c_323, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.61/1.33  tff(c_322, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.61/1.33  tff(c_359, plain, (![B_106, A_107]: (r1_tsep_1(B_106, A_107) | ~r1_tsep_1(A_107, B_106) | ~l1_struct_0(B_106) | ~l1_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.33  tff(c_361, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_322, c_359])).
% 2.61/1.33  tff(c_364, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_323, c_361])).
% 2.61/1.33  tff(c_365, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_364])).
% 2.61/1.33  tff(c_368, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_365])).
% 2.61/1.33  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_368])).
% 2.61/1.33  tff(c_373, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_364])).
% 2.61/1.33  tff(c_377, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_373])).
% 2.61/1.33  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_377])).
% 2.61/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.33  
% 2.61/1.33  Inference rules
% 2.61/1.33  ----------------------
% 2.61/1.33  #Ref     : 0
% 2.61/1.33  #Sup     : 52
% 2.61/1.33  #Fact    : 0
% 2.61/1.33  #Define  : 0
% 2.61/1.33  #Split   : 11
% 2.61/1.33  #Chain   : 0
% 2.61/1.33  #Close   : 0
% 2.61/1.33  
% 2.61/1.33  Ordering : KBO
% 2.61/1.33  
% 2.61/1.33  Simplification rules
% 2.61/1.33  ----------------------
% 2.61/1.33  #Subsume      : 0
% 2.61/1.33  #Demod        : 36
% 2.61/1.33  #Tautology    : 19
% 2.61/1.33  #SimpNegUnit  : 3
% 2.61/1.33  #BackRed      : 0
% 2.61/1.33  
% 2.61/1.33  #Partial instantiations: 0
% 2.61/1.33  #Strategies tried      : 1
% 2.61/1.33  
% 2.61/1.33  Timing (in seconds)
% 2.61/1.33  ----------------------
% 2.61/1.34  Preprocessing        : 0.28
% 2.61/1.34  Parsing              : 0.16
% 2.61/1.34  CNF conversion       : 0.02
% 2.61/1.34  Main loop            : 0.24
% 2.61/1.34  Inferencing          : 0.10
% 2.61/1.34  Reduction            : 0.07
% 2.61/1.34  Demodulation         : 0.05
% 2.61/1.34  BG Simplification    : 0.01
% 2.61/1.34  Subsumption          : 0.04
% 2.61/1.34  Abstraction          : 0.01
% 2.61/1.34  MUC search           : 0.00
% 2.61/1.34  Cooper               : 0.00
% 2.61/1.34  Total                : 0.56
% 2.61/1.34  Index Insertion      : 0.00
% 2.61/1.34  Index Deletion       : 0.00
% 2.61/1.34  Index Matching       : 0.00
% 2.61/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
