%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:48 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 203 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  193 ( 568 expanded)
%              Number of equality atoms :   24 (  70 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_63,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_385,plain,(
    ! [B_90,A_91] :
      ( v2_tops_1(B_90,A_91)
      | k1_tops_1(A_91,B_90) != k1_xboole_0
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_392,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_385])).

tff(c_396,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_392])).

tff(c_397,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_396])).

tff(c_199,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tops_1(A_74,B_75),B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_204,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_199])).

tff(c_208,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_204])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_262,plain,(
    ! [A_79,B_80] :
      ( v3_pre_topc(k1_tops_1(A_79,B_80),A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_267,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_262])).

tff(c_271,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_267])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_126,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_74,c_126])).

tff(c_20,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_272,plain,(
    ! [A_81,A_82] :
      ( r1_tarski(A_81,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_81,A_82)
      | ~ r1_tarski(A_82,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_146,c_20])).

tff(c_274,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_208,c_272])).

tff(c_285,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_274])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    ! [C_39] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_39
      | ~ v3_pre_topc(C_39,'#skF_3')
      | ~ r1_tarski(C_39,'#skF_4')
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_158,plain,(
    ! [C_65] :
      ( k1_xboole_0 = C_65
      | ~ v3_pre_topc(C_65,'#skF_3')
      | ~ r1_tarski(C_65,'#skF_4')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_60])).

tff(c_402,plain,(
    ! [A_92] :
      ( k1_xboole_0 = A_92
      | ~ v3_pre_topc(A_92,'#skF_3')
      | ~ r1_tarski(A_92,'#skF_4')
      | ~ r1_tarski(A_92,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_158])).

tff(c_409,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_285,c_402])).

tff(c_427,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_271,c_409])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_427])).

tff(c_430,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_431,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_48,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_453,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_48])).

tff(c_596,plain,(
    ! [A_122,B_123] :
      ( r1_tarski(k1_tops_1(A_122,B_123),B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_598,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_453,c_596])).

tff(c_606,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_598])).

tff(c_459,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102,B_103),A_102)
      | r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_469,plain,(
    ! [A_102,B_103] :
      ( ~ v1_xboole_0(A_102)
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_459,c_2])).

tff(c_471,plain,(
    ! [B_106,A_107] :
      ( B_106 = A_107
      | ~ r1_tarski(B_106,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_482,plain,(
    ! [B_103,A_102] :
      ( B_103 = A_102
      | ~ r1_tarski(B_103,A_102)
      | ~ v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_469,c_471])).

tff(c_621,plain,
    ( k1_tops_1('#skF_3','#skF_5') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_606,c_482])).

tff(c_646,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_434,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_44])).

tff(c_46,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_441,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_46])).

tff(c_792,plain,(
    ! [A_136,B_137] :
      ( k1_tops_1(A_136,B_137) = k1_xboole_0
      | ~ v2_tops_1(B_137,A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_802,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_792])).

tff(c_810,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_431,c_802])).

tff(c_955,plain,(
    ! [B_144,A_145,C_146] :
      ( r1_tarski(B_144,k1_tops_1(A_145,C_146))
      | ~ r1_tarski(B_144,C_146)
      | ~ v3_pre_topc(B_144,A_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_962,plain,(
    ! [B_144] :
      ( r1_tarski(B_144,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski(B_144,'#skF_4')
      | ~ v3_pre_topc(B_144,'#skF_3')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_955])).

tff(c_1048,plain,(
    ! [B_151] :
      ( r1_tarski(B_151,k1_xboole_0)
      | ~ r1_tarski(B_151,'#skF_4')
      | ~ v3_pre_topc(B_151,'#skF_3')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_810,c_962])).

tff(c_1051,plain,
    ( r1_tarski('#skF_5',k1_xboole_0)
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_453,c_1048])).

tff(c_1061,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_441,c_1051])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_571,plain,(
    ! [C_118,B_119,A_120] :
      ( r2_hidden(C_118,B_119)
      | ~ r2_hidden(C_118,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_734,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_1'(A_132),B_133)
      | ~ r1_tarski(A_132,B_133)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_4,c_571])).

tff(c_741,plain,(
    ! [B_133,A_132] :
      ( ~ v1_xboole_0(B_133)
      | ~ r1_tarski(A_132,B_133)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_734,c_2])).

tff(c_1076,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1061,c_741])).

tff(c_1095,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1076])).

tff(c_1097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_1095])).

tff(c_1099,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_537,plain,(
    ! [B_114,A_115] :
      ( B_114 = A_115
      | ~ r1_tarski(B_114,A_115)
      | ~ v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_469,c_471])).

tff(c_567,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ v1_xboole_0(B_116)
      | ~ v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_469,c_537])).

tff(c_570,plain,(
    ! [A_117] :
      ( k1_xboole_0 = A_117
      | ~ v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_12,c_567])).

tff(c_1102,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1099,c_570])).

tff(c_1108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_1102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/2.00  
% 3.95/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/2.00  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.95/2.00  
% 3.95/2.00  %Foreground sorts:
% 3.95/2.00  
% 3.95/2.00  
% 3.95/2.00  %Background operators:
% 3.95/2.00  
% 3.95/2.00  
% 3.95/2.00  %Foreground operators:
% 3.95/2.00  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.95/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.95/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/2.00  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.95/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.95/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/2.00  tff('#skF_5', type, '#skF_5': $i).
% 3.95/2.00  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.95/2.00  tff('#skF_3', type, '#skF_3': $i).
% 3.95/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/2.00  tff('#skF_4', type, '#skF_4': $i).
% 3.95/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.95/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.95/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.95/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.95/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/2.00  
% 3.95/2.03  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.95/2.03  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.95/2.03  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.95/2.03  tff(f_63, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.95/2.03  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/2.03  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.95/2.03  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.95/2.03  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.95/2.03  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.95/2.03  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.95/2.03  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.95/2.03  tff(c_42, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_63, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.95/2.03  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_385, plain, (![B_90, A_91]: (v2_tops_1(B_90, A_91) | k1_tops_1(A_91, B_90)!=k1_xboole_0 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.95/2.03  tff(c_392, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_385])).
% 3.95/2.03  tff(c_396, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_392])).
% 3.95/2.03  tff(c_397, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_63, c_396])).
% 3.95/2.03  tff(c_199, plain, (![A_74, B_75]: (r1_tarski(k1_tops_1(A_74, B_75), B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/2.03  tff(c_204, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_199])).
% 3.95/2.03  tff(c_208, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_204])).
% 3.95/2.03  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_262, plain, (![A_79, B_80]: (v3_pre_topc(k1_tops_1(A_79, B_80), A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/2.03  tff(c_267, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_262])).
% 3.95/2.03  tff(c_271, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_267])).
% 3.95/2.03  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/2.03  tff(c_70, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.95/2.03  tff(c_74, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_70])).
% 3.95/2.03  tff(c_126, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.95/2.03  tff(c_146, plain, (![A_64]: (r1_tarski(A_64, u1_struct_0('#skF_3')) | ~r1_tarski(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_126])).
% 3.95/2.03  tff(c_20, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.95/2.03  tff(c_272, plain, (![A_81, A_82]: (r1_tarski(A_81, u1_struct_0('#skF_3')) | ~r1_tarski(A_81, A_82) | ~r1_tarski(A_82, '#skF_4'))), inference(resolution, [status(thm)], [c_146, c_20])).
% 3.95/2.03  tff(c_274, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_208, c_272])).
% 3.95/2.03  tff(c_285, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_274])).
% 3.95/2.03  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.95/2.03  tff(c_60, plain, (![C_39]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_39 | ~v3_pre_topc(C_39, '#skF_3') | ~r1_tarski(C_39, '#skF_4') | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_158, plain, (![C_65]: (k1_xboole_0=C_65 | ~v3_pre_topc(C_65, '#skF_3') | ~r1_tarski(C_65, '#skF_4') | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_63, c_60])).
% 3.95/2.03  tff(c_402, plain, (![A_92]: (k1_xboole_0=A_92 | ~v3_pre_topc(A_92, '#skF_3') | ~r1_tarski(A_92, '#skF_4') | ~r1_tarski(A_92, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_158])).
% 3.95/2.03  tff(c_409, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_285, c_402])).
% 3.95/2.03  tff(c_427, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_208, c_271, c_409])).
% 3.95/2.03  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_427])).
% 3.95/2.03  tff(c_430, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 3.95/2.03  tff(c_431, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.95/2.03  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_453, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_48])).
% 3.95/2.03  tff(c_596, plain, (![A_122, B_123]: (r1_tarski(k1_tops_1(A_122, B_123), B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/2.03  tff(c_598, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_453, c_596])).
% 3.95/2.03  tff(c_606, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_598])).
% 3.95/2.03  tff(c_459, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102, B_103), A_102) | r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.95/2.03  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/2.03  tff(c_469, plain, (![A_102, B_103]: (~v1_xboole_0(A_102) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_459, c_2])).
% 3.95/2.03  tff(c_471, plain, (![B_106, A_107]: (B_106=A_107 | ~r1_tarski(B_106, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/2.03  tff(c_482, plain, (![B_103, A_102]: (B_103=A_102 | ~r1_tarski(B_103, A_102) | ~v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_469, c_471])).
% 3.95/2.03  tff(c_621, plain, (k1_tops_1('#skF_3', '#skF_5')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_606, c_482])).
% 3.95/2.03  tff(c_646, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_621])).
% 3.95/2.03  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/2.03  tff(c_44, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_434, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_44])).
% 3.95/2.03  tff(c_46, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.95/2.03  tff(c_441, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_46])).
% 3.95/2.03  tff(c_792, plain, (![A_136, B_137]: (k1_tops_1(A_136, B_137)=k1_xboole_0 | ~v2_tops_1(B_137, A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.95/2.03  tff(c_802, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_792])).
% 3.95/2.03  tff(c_810, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_431, c_802])).
% 3.95/2.03  tff(c_955, plain, (![B_144, A_145, C_146]: (r1_tarski(B_144, k1_tops_1(A_145, C_146)) | ~r1_tarski(B_144, C_146) | ~v3_pre_topc(B_144, A_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.95/2.03  tff(c_962, plain, (![B_144]: (r1_tarski(B_144, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski(B_144, '#skF_4') | ~v3_pre_topc(B_144, '#skF_3') | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_955])).
% 3.95/2.03  tff(c_1048, plain, (![B_151]: (r1_tarski(B_151, k1_xboole_0) | ~r1_tarski(B_151, '#skF_4') | ~v3_pre_topc(B_151, '#skF_3') | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_810, c_962])).
% 3.95/2.03  tff(c_1051, plain, (r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_453, c_1048])).
% 3.95/2.03  tff(c_1061, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_434, c_441, c_1051])).
% 3.95/2.03  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/2.03  tff(c_571, plain, (![C_118, B_119, A_120]: (r2_hidden(C_118, B_119) | ~r2_hidden(C_118, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.95/2.03  tff(c_734, plain, (![A_132, B_133]: (r2_hidden('#skF_1'(A_132), B_133) | ~r1_tarski(A_132, B_133) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_4, c_571])).
% 3.95/2.03  tff(c_741, plain, (![B_133, A_132]: (~v1_xboole_0(B_133) | ~r1_tarski(A_132, B_133) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_734, c_2])).
% 3.95/2.03  tff(c_1076, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1061, c_741])).
% 3.95/2.03  tff(c_1095, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1076])).
% 3.95/2.03  tff(c_1097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_1095])).
% 3.95/2.03  tff(c_1099, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_621])).
% 3.95/2.03  tff(c_537, plain, (![B_114, A_115]: (B_114=A_115 | ~r1_tarski(B_114, A_115) | ~v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_469, c_471])).
% 3.95/2.03  tff(c_567, plain, (![B_116, A_117]: (B_116=A_117 | ~v1_xboole_0(B_116) | ~v1_xboole_0(A_117))), inference(resolution, [status(thm)], [c_469, c_537])).
% 3.95/2.03  tff(c_570, plain, (![A_117]: (k1_xboole_0=A_117 | ~v1_xboole_0(A_117))), inference(resolution, [status(thm)], [c_12, c_567])).
% 3.95/2.03  tff(c_1102, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1099, c_570])).
% 3.95/2.03  tff(c_1108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_1102])).
% 3.95/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/2.03  
% 3.95/2.03  Inference rules
% 3.95/2.03  ----------------------
% 3.95/2.03  #Ref     : 0
% 3.95/2.03  #Sup     : 234
% 3.95/2.03  #Fact    : 0
% 3.95/2.03  #Define  : 0
% 3.95/2.03  #Split   : 16
% 3.95/2.03  #Chain   : 0
% 3.95/2.03  #Close   : 0
% 3.95/2.03  
% 3.95/2.03  Ordering : KBO
% 3.95/2.03  
% 3.95/2.03  Simplification rules
% 3.95/2.03  ----------------------
% 3.95/2.03  #Subsume      : 101
% 3.95/2.03  #Demod        : 73
% 3.95/2.03  #Tautology    : 42
% 3.95/2.03  #SimpNegUnit  : 11
% 3.95/2.03  #BackRed      : 3
% 3.95/2.03  
% 3.95/2.03  #Partial instantiations: 0
% 3.95/2.03  #Strategies tried      : 1
% 3.95/2.03  
% 3.95/2.03  Timing (in seconds)
% 3.95/2.03  ----------------------
% 3.95/2.04  Preprocessing        : 0.49
% 3.95/2.04  Parsing              : 0.25
% 3.95/2.04  CNF conversion       : 0.04
% 3.95/2.04  Main loop            : 0.65
% 3.95/2.04  Inferencing          : 0.22
% 3.95/2.04  Reduction            : 0.19
% 3.95/2.04  Demodulation         : 0.13
% 3.95/2.04  BG Simplification    : 0.03
% 3.95/2.04  Subsumption          : 0.15
% 3.95/2.04  Abstraction          : 0.03
% 3.95/2.04  MUC search           : 0.00
% 3.95/2.04  Cooper               : 0.00
% 3.95/2.04  Total                : 1.20
% 3.95/2.04  Index Insertion      : 0.00
% 3.95/2.04  Index Deletion       : 0.00
% 3.95/2.04  Index Matching       : 0.00
% 3.95/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
