%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:46 EST 2020

% Result     : Theorem 11.08s
% Output     : CNFRefutation 11.08s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 256 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  173 ( 707 expanded)
%              Number of equality atoms :   33 ( 156 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_197,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r2_hidden('#skF_1'(A_74,B_75,C_76),C_76)
      | r2_hidden('#skF_2'(A_74,B_75,C_76),C_76)
      | k3_xboole_0(A_74,B_75) = C_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_206,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_197])).

tff(c_108,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_1'(A_66,B_67,C_68),B_67)
      | r2_hidden('#skF_2'(A_66,B_67,C_68),C_68)
      | k3_xboole_0(A_66,B_67) = C_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_895,plain,(
    ! [A_155,B_156,A_157,B_158] :
      ( r2_hidden('#skF_2'(A_155,B_156,k3_xboole_0(A_157,B_158)),B_158)
      | r2_hidden('#skF_1'(A_155,B_156,k3_xboole_0(A_157,B_158)),B_156)
      | k3_xboole_0(A_157,B_158) = k3_xboole_0(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_929,plain,(
    ! [B_158,B_156,A_157] :
      ( ~ r2_hidden('#skF_2'(B_158,B_156,k3_xboole_0(A_157,B_158)),B_156)
      | r2_hidden('#skF_1'(B_158,B_156,k3_xboole_0(A_157,B_158)),B_156)
      | k3_xboole_0(B_158,B_156) = k3_xboole_0(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_895,c_10])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_506,plain,(
    ! [A_115,A_116,B_117,C_118] :
      ( r2_hidden('#skF_1'(A_115,k3_xboole_0(A_116,B_117),C_118),A_116)
      | r2_hidden('#skF_2'(A_115,k3_xboole_0(A_116,B_117),C_118),C_118)
      | k3_xboole_0(A_115,k3_xboole_0(A_116,B_117)) = C_118 ) ),
    inference(resolution,[status(thm)],[c_108,c_6])).

tff(c_549,plain,(
    ! [A_116,B_2,A_1,A_115,B_117] :
      ( r2_hidden('#skF_2'(A_115,k3_xboole_0(A_116,B_117),k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_115,k3_xboole_0(A_116,B_117),k3_xboole_0(A_1,B_2)),A_116)
      | k3_xboole_0(A_115,k3_xboole_0(A_116,B_117)) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_506,c_4])).

tff(c_219,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden('#skF_1'(A_79,B_80,C_81),A_79)
      | r2_hidden('#skF_2'(A_79,B_80,C_81),C_81)
      | k3_xboole_0(A_79,B_80) = C_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_244,plain,(
    ! [A_79,B_80,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_79,B_80,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_79,B_80,k3_xboole_0(A_1,B_2)),A_79)
      | k3_xboole_0(A_79,B_80) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_219,c_4])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1174,plain,(
    ! [A_191,B_192,A_193,B_194] :
      ( r2_hidden('#skF_2'(A_191,B_192,k3_xboole_0(A_193,B_194)),k3_xboole_0(A_193,B_194))
      | k3_xboole_0(A_193,B_194) = k3_xboole_0(A_191,B_192)
      | ~ r2_hidden('#skF_1'(A_191,B_192,k3_xboole_0(A_193,B_194)),B_194)
      | ~ r2_hidden('#skF_1'(A_191,B_192,k3_xboole_0(A_193,B_194)),A_193) ) ),
    inference(resolution,[status(thm)],[c_2,c_197])).

tff(c_5507,plain,(
    ! [A_529,B_530,A_531,B_532] :
      ( r2_hidden('#skF_2'(A_529,B_530,k3_xboole_0(A_531,B_532)),B_532)
      | k3_xboole_0(A_531,B_532) = k3_xboole_0(A_529,B_530)
      | ~ r2_hidden('#skF_1'(A_529,B_530,k3_xboole_0(A_531,B_532)),B_532)
      | ~ r2_hidden('#skF_1'(A_529,B_530,k3_xboole_0(A_531,B_532)),A_531) ) ),
    inference(resolution,[status(thm)],[c_1174,c_4])).

tff(c_5920,plain,(
    ! [A_542,B_543,A_544] :
      ( ~ r2_hidden('#skF_1'(A_542,B_543,k3_xboole_0(A_544,A_542)),A_544)
      | r2_hidden('#skF_2'(A_542,B_543,k3_xboole_0(A_544,A_542)),A_542)
      | k3_xboole_0(A_544,A_542) = k3_xboole_0(A_542,B_543) ) ),
    inference(resolution,[status(thm)],[c_244,c_5507])).

tff(c_6056,plain,(
    ! [B_2,A_116,B_117] :
      ( r2_hidden('#skF_2'(B_2,k3_xboole_0(A_116,B_117),k3_xboole_0(A_116,B_2)),B_2)
      | k3_xboole_0(B_2,k3_xboole_0(A_116,B_117)) = k3_xboole_0(A_116,B_2) ) ),
    inference(resolution,[status(thm)],[c_549,c_5920])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_240,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_2'(A_79,B_80,A_79),A_79)
      | k3_xboole_0(A_79,B_80) = A_79 ) ),
    inference(resolution,[status(thm)],[c_219,c_14])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_314,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_1'(A_102,B_103,C_104),A_102)
      | ~ r2_hidden('#skF_2'(A_102,B_103,C_104),B_103)
      | ~ r2_hidden('#skF_2'(A_102,B_103,C_104),A_102)
      | k3_xboole_0(A_102,B_103) = C_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_339,plain,(
    ! [A_105,C_106] :
      ( ~ r2_hidden('#skF_2'(A_105,C_106,C_106),A_105)
      | r2_hidden('#skF_1'(A_105,C_106,C_106),A_105)
      | k3_xboole_0(A_105,C_106) = C_106 ) ),
    inference(resolution,[status(thm)],[c_18,c_314])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_384,plain,(
    ! [A_110] :
      ( ~ r2_hidden('#skF_2'(A_110,A_110,A_110),A_110)
      | k3_xboole_0(A_110,A_110) = A_110 ) ),
    inference(resolution,[status(thm)],[c_339,c_8])).

tff(c_401,plain,(
    ! [B_80] : k3_xboole_0(B_80,B_80) = B_80 ),
    inference(resolution,[status(thm)],[c_240,c_384])).

tff(c_207,plain,(
    ! [A_74,B_75,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_74,B_75,k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2))
      | k3_xboole_0(A_74,B_75) = k3_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_74,B_75,k3_xboole_0(A_1,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_74,B_75,k3_xboole_0(A_1,B_2)),A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_197])).

tff(c_268,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r2_hidden('#skF_1'(A_90,B_91,C_92),C_92)
      | ~ r2_hidden('#skF_2'(A_90,B_91,C_92),B_91)
      | ~ r2_hidden('#skF_2'(A_90,B_91,C_92),A_90)
      | k3_xboole_0(A_90,B_91) = C_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1681,plain,(
    ! [A_227,B_228,A_229,B_230] :
      ( ~ r2_hidden('#skF_2'(A_227,B_228,k3_xboole_0(A_229,B_230)),B_228)
      | ~ r2_hidden('#skF_2'(A_227,B_228,k3_xboole_0(A_229,B_230)),A_227)
      | k3_xboole_0(A_229,B_230) = k3_xboole_0(A_227,B_228)
      | ~ r2_hidden('#skF_1'(A_227,B_228,k3_xboole_0(A_229,B_230)),B_230)
      | ~ r2_hidden('#skF_1'(A_227,B_228,k3_xboole_0(A_229,B_230)),A_229) ) ),
    inference(resolution,[status(thm)],[c_2,c_268])).

tff(c_8698,plain,(
    ! [A_665,A_666,B_667] :
      ( ~ r2_hidden('#skF_2'(A_665,k3_xboole_0(A_666,B_667),k3_xboole_0(A_666,B_667)),A_665)
      | k3_xboole_0(A_665,k3_xboole_0(A_666,B_667)) = k3_xboole_0(A_666,B_667)
      | ~ r2_hidden('#skF_1'(A_665,k3_xboole_0(A_666,B_667),k3_xboole_0(A_666,B_667)),B_667)
      | ~ r2_hidden('#skF_1'(A_665,k3_xboole_0(A_666,B_667),k3_xboole_0(A_666,B_667)),A_666) ) ),
    inference(resolution,[status(thm)],[c_207,c_1681])).

tff(c_8795,plain,(
    ! [A_665,B_80] :
      ( ~ r2_hidden('#skF_2'(A_665,B_80,k3_xboole_0(B_80,B_80)),A_665)
      | k3_xboole_0(A_665,k3_xboole_0(B_80,B_80)) = k3_xboole_0(B_80,B_80)
      | ~ r2_hidden('#skF_1'(A_665,k3_xboole_0(B_80,B_80),k3_xboole_0(B_80,B_80)),B_80)
      | ~ r2_hidden('#skF_1'(A_665,k3_xboole_0(B_80,B_80),k3_xboole_0(B_80,B_80)),B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_8698])).

tff(c_8867,plain,(
    ! [A_668,B_669] :
      ( ~ r2_hidden('#skF_2'(A_668,B_669,B_669),A_668)
      | k3_xboole_0(A_668,B_669) = B_669
      | ~ r2_hidden('#skF_1'(A_668,B_669,B_669),B_669)
      | ~ r2_hidden('#skF_1'(A_668,B_669,B_669),B_669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_401,c_401,c_401,c_401,c_401,c_401,c_8795])).

tff(c_9030,plain,(
    ! [B_670,A_671] :
      ( ~ r2_hidden('#skF_1'(B_670,k3_xboole_0(A_671,B_670),k3_xboole_0(A_671,B_670)),k3_xboole_0(A_671,B_670))
      | k3_xboole_0(B_670,k3_xboole_0(A_671,B_670)) = k3_xboole_0(A_671,B_670) ) ),
    inference(resolution,[status(thm)],[c_6056,c_8867])).

tff(c_11353,plain,(
    ! [B_686,A_687] :
      ( ~ r2_hidden('#skF_2'(B_686,k3_xboole_0(A_687,B_686),k3_xboole_0(A_687,B_686)),k3_xboole_0(A_687,B_686))
      | k3_xboole_0(B_686,k3_xboole_0(A_687,B_686)) = k3_xboole_0(A_687,B_686) ) ),
    inference(resolution,[status(thm)],[c_929,c_9030])).

tff(c_11464,plain,(
    ! [A_688,A_689] : k3_xboole_0(A_688,k3_xboole_0(A_689,A_688)) = k3_xboole_0(A_689,A_688) ),
    inference(resolution,[status(thm)],[c_206,c_11353])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12716,plain,(
    ! [A_689,A_688] : r1_tarski(k3_xboole_0(A_689,A_688),A_688) ),
    inference(superposition,[status(thm),theory(equality)],[c_11464,c_20])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [A_50,B_51] :
      ( v1_relat_1(A_50)
      | ~ v1_relat_1(B_51)
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_79,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k3_xboole_0(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [C_27,A_21,B_25] :
      ( r1_tarski(k5_relat_1(C_27,A_21),k5_relat_1(C_27,B_25))
      | ~ r1_tarski(A_21,B_25)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k3_xboole_0(B_58,C_59))
      | ~ r1_tarski(A_57,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_98,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_36])).

tff(c_129,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_132,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_129])).

tff(c_135,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_20,c_132])).

tff(c_138,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_138])).

tff(c_143,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_147,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_150,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_147])).

tff(c_155,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_179,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_155])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_179])).

tff(c_184,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_13146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12716,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:38 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.08/3.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.08/3.94  
% 11.08/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.08/3.94  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 11.08/3.94  
% 11.08/3.94  %Foreground sorts:
% 11.08/3.94  
% 11.08/3.94  
% 11.08/3.94  %Background operators:
% 11.08/3.94  
% 11.08/3.94  
% 11.08/3.94  %Foreground operators:
% 11.08/3.94  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.08/3.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.08/3.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.08/3.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.08/3.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.08/3.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.08/3.94  tff('#skF_5', type, '#skF_5': $i).
% 11.08/3.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.08/3.94  tff('#skF_3', type, '#skF_3': $i).
% 11.08/3.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.08/3.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.08/3.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.08/3.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.08/3.94  tff('#skF_4', type, '#skF_4': $i).
% 11.08/3.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.08/3.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.08/3.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.08/3.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.08/3.94  
% 11.08/3.96  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.08/3.96  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.08/3.96  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 11.08/3.96  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.08/3.96  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.08/3.96  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 11.08/3.96  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 11.08/3.96  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_197, plain, (![A_74, B_75, C_76]: (~r2_hidden('#skF_1'(A_74, B_75, C_76), C_76) | r2_hidden('#skF_2'(A_74, B_75, C_76), C_76) | k3_xboole_0(A_74, B_75)=C_76)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_206, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_197])).
% 11.08/3.96  tff(c_108, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_1'(A_66, B_67, C_68), B_67) | r2_hidden('#skF_2'(A_66, B_67, C_68), C_68) | k3_xboole_0(A_66, B_67)=C_68)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_895, plain, (![A_155, B_156, A_157, B_158]: (r2_hidden('#skF_2'(A_155, B_156, k3_xboole_0(A_157, B_158)), B_158) | r2_hidden('#skF_1'(A_155, B_156, k3_xboole_0(A_157, B_158)), B_156) | k3_xboole_0(A_157, B_158)=k3_xboole_0(A_155, B_156))), inference(resolution, [status(thm)], [c_108, c_4])).
% 11.08/3.96  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_929, plain, (![B_158, B_156, A_157]: (~r2_hidden('#skF_2'(B_158, B_156, k3_xboole_0(A_157, B_158)), B_156) | r2_hidden('#skF_1'(B_158, B_156, k3_xboole_0(A_157, B_158)), B_156) | k3_xboole_0(B_158, B_156)=k3_xboole_0(A_157, B_158))), inference(resolution, [status(thm)], [c_895, c_10])).
% 11.08/3.96  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_506, plain, (![A_115, A_116, B_117, C_118]: (r2_hidden('#skF_1'(A_115, k3_xboole_0(A_116, B_117), C_118), A_116) | r2_hidden('#skF_2'(A_115, k3_xboole_0(A_116, B_117), C_118), C_118) | k3_xboole_0(A_115, k3_xboole_0(A_116, B_117))=C_118)), inference(resolution, [status(thm)], [c_108, c_6])).
% 11.08/3.96  tff(c_549, plain, (![A_116, B_2, A_1, A_115, B_117]: (r2_hidden('#skF_2'(A_115, k3_xboole_0(A_116, B_117), k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_115, k3_xboole_0(A_116, B_117), k3_xboole_0(A_1, B_2)), A_116) | k3_xboole_0(A_115, k3_xboole_0(A_116, B_117))=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_506, c_4])).
% 11.08/3.96  tff(c_219, plain, (![A_79, B_80, C_81]: (r2_hidden('#skF_1'(A_79, B_80, C_81), A_79) | r2_hidden('#skF_2'(A_79, B_80, C_81), C_81) | k3_xboole_0(A_79, B_80)=C_81)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_244, plain, (![A_79, B_80, A_1, B_2]: (r2_hidden('#skF_2'(A_79, B_80, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_79, B_80, k3_xboole_0(A_1, B_2)), A_79) | k3_xboole_0(A_79, B_80)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_219, c_4])).
% 11.08/3.96  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_1174, plain, (![A_191, B_192, A_193, B_194]: (r2_hidden('#skF_2'(A_191, B_192, k3_xboole_0(A_193, B_194)), k3_xboole_0(A_193, B_194)) | k3_xboole_0(A_193, B_194)=k3_xboole_0(A_191, B_192) | ~r2_hidden('#skF_1'(A_191, B_192, k3_xboole_0(A_193, B_194)), B_194) | ~r2_hidden('#skF_1'(A_191, B_192, k3_xboole_0(A_193, B_194)), A_193))), inference(resolution, [status(thm)], [c_2, c_197])).
% 11.08/3.96  tff(c_5507, plain, (![A_529, B_530, A_531, B_532]: (r2_hidden('#skF_2'(A_529, B_530, k3_xboole_0(A_531, B_532)), B_532) | k3_xboole_0(A_531, B_532)=k3_xboole_0(A_529, B_530) | ~r2_hidden('#skF_1'(A_529, B_530, k3_xboole_0(A_531, B_532)), B_532) | ~r2_hidden('#skF_1'(A_529, B_530, k3_xboole_0(A_531, B_532)), A_531))), inference(resolution, [status(thm)], [c_1174, c_4])).
% 11.08/3.96  tff(c_5920, plain, (![A_542, B_543, A_544]: (~r2_hidden('#skF_1'(A_542, B_543, k3_xboole_0(A_544, A_542)), A_544) | r2_hidden('#skF_2'(A_542, B_543, k3_xboole_0(A_544, A_542)), A_542) | k3_xboole_0(A_544, A_542)=k3_xboole_0(A_542, B_543))), inference(resolution, [status(thm)], [c_244, c_5507])).
% 11.08/3.96  tff(c_6056, plain, (![B_2, A_116, B_117]: (r2_hidden('#skF_2'(B_2, k3_xboole_0(A_116, B_117), k3_xboole_0(A_116, B_2)), B_2) | k3_xboole_0(B_2, k3_xboole_0(A_116, B_117))=k3_xboole_0(A_116, B_2))), inference(resolution, [status(thm)], [c_549, c_5920])).
% 11.08/3.96  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_240, plain, (![A_79, B_80]: (r2_hidden('#skF_2'(A_79, B_80, A_79), A_79) | k3_xboole_0(A_79, B_80)=A_79)), inference(resolution, [status(thm)], [c_219, c_14])).
% 11.08/3.96  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_314, plain, (![A_102, B_103, C_104]: (r2_hidden('#skF_1'(A_102, B_103, C_104), A_102) | ~r2_hidden('#skF_2'(A_102, B_103, C_104), B_103) | ~r2_hidden('#skF_2'(A_102, B_103, C_104), A_102) | k3_xboole_0(A_102, B_103)=C_104)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_339, plain, (![A_105, C_106]: (~r2_hidden('#skF_2'(A_105, C_106, C_106), A_105) | r2_hidden('#skF_1'(A_105, C_106, C_106), A_105) | k3_xboole_0(A_105, C_106)=C_106)), inference(resolution, [status(thm)], [c_18, c_314])).
% 11.08/3.96  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_384, plain, (![A_110]: (~r2_hidden('#skF_2'(A_110, A_110, A_110), A_110) | k3_xboole_0(A_110, A_110)=A_110)), inference(resolution, [status(thm)], [c_339, c_8])).
% 11.08/3.96  tff(c_401, plain, (![B_80]: (k3_xboole_0(B_80, B_80)=B_80)), inference(resolution, [status(thm)], [c_240, c_384])).
% 11.08/3.96  tff(c_207, plain, (![A_74, B_75, A_1, B_2]: (r2_hidden('#skF_2'(A_74, B_75, k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2)) | k3_xboole_0(A_74, B_75)=k3_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_74, B_75, k3_xboole_0(A_1, B_2)), B_2) | ~r2_hidden('#skF_1'(A_74, B_75, k3_xboole_0(A_1, B_2)), A_1))), inference(resolution, [status(thm)], [c_2, c_197])).
% 11.08/3.96  tff(c_268, plain, (![A_90, B_91, C_92]: (~r2_hidden('#skF_1'(A_90, B_91, C_92), C_92) | ~r2_hidden('#skF_2'(A_90, B_91, C_92), B_91) | ~r2_hidden('#skF_2'(A_90, B_91, C_92), A_90) | k3_xboole_0(A_90, B_91)=C_92)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.08/3.96  tff(c_1681, plain, (![A_227, B_228, A_229, B_230]: (~r2_hidden('#skF_2'(A_227, B_228, k3_xboole_0(A_229, B_230)), B_228) | ~r2_hidden('#skF_2'(A_227, B_228, k3_xboole_0(A_229, B_230)), A_227) | k3_xboole_0(A_229, B_230)=k3_xboole_0(A_227, B_228) | ~r2_hidden('#skF_1'(A_227, B_228, k3_xboole_0(A_229, B_230)), B_230) | ~r2_hidden('#skF_1'(A_227, B_228, k3_xboole_0(A_229, B_230)), A_229))), inference(resolution, [status(thm)], [c_2, c_268])).
% 11.08/3.96  tff(c_8698, plain, (![A_665, A_666, B_667]: (~r2_hidden('#skF_2'(A_665, k3_xboole_0(A_666, B_667), k3_xboole_0(A_666, B_667)), A_665) | k3_xboole_0(A_665, k3_xboole_0(A_666, B_667))=k3_xboole_0(A_666, B_667) | ~r2_hidden('#skF_1'(A_665, k3_xboole_0(A_666, B_667), k3_xboole_0(A_666, B_667)), B_667) | ~r2_hidden('#skF_1'(A_665, k3_xboole_0(A_666, B_667), k3_xboole_0(A_666, B_667)), A_666))), inference(resolution, [status(thm)], [c_207, c_1681])).
% 11.08/3.96  tff(c_8795, plain, (![A_665, B_80]: (~r2_hidden('#skF_2'(A_665, B_80, k3_xboole_0(B_80, B_80)), A_665) | k3_xboole_0(A_665, k3_xboole_0(B_80, B_80))=k3_xboole_0(B_80, B_80) | ~r2_hidden('#skF_1'(A_665, k3_xboole_0(B_80, B_80), k3_xboole_0(B_80, B_80)), B_80) | ~r2_hidden('#skF_1'(A_665, k3_xboole_0(B_80, B_80), k3_xboole_0(B_80, B_80)), B_80))), inference(superposition, [status(thm), theory('equality')], [c_401, c_8698])).
% 11.08/3.96  tff(c_8867, plain, (![A_668, B_669]: (~r2_hidden('#skF_2'(A_668, B_669, B_669), A_668) | k3_xboole_0(A_668, B_669)=B_669 | ~r2_hidden('#skF_1'(A_668, B_669, B_669), B_669) | ~r2_hidden('#skF_1'(A_668, B_669, B_669), B_669))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_401, c_401, c_401, c_401, c_401, c_401, c_8795])).
% 11.08/3.96  tff(c_9030, plain, (![B_670, A_671]: (~r2_hidden('#skF_1'(B_670, k3_xboole_0(A_671, B_670), k3_xboole_0(A_671, B_670)), k3_xboole_0(A_671, B_670)) | k3_xboole_0(B_670, k3_xboole_0(A_671, B_670))=k3_xboole_0(A_671, B_670))), inference(resolution, [status(thm)], [c_6056, c_8867])).
% 11.08/3.96  tff(c_11353, plain, (![B_686, A_687]: (~r2_hidden('#skF_2'(B_686, k3_xboole_0(A_687, B_686), k3_xboole_0(A_687, B_686)), k3_xboole_0(A_687, B_686)) | k3_xboole_0(B_686, k3_xboole_0(A_687, B_686))=k3_xboole_0(A_687, B_686))), inference(resolution, [status(thm)], [c_929, c_9030])).
% 11.08/3.96  tff(c_11464, plain, (![A_688, A_689]: (k3_xboole_0(A_688, k3_xboole_0(A_689, A_688))=k3_xboole_0(A_689, A_688))), inference(resolution, [status(thm)], [c_206, c_11353])).
% 11.08/3.96  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.08/3.96  tff(c_12716, plain, (![A_689, A_688]: (r1_tarski(k3_xboole_0(A_689, A_688), A_688))), inference(superposition, [status(thm), theory('equality')], [c_11464, c_20])).
% 11.08/3.96  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.08/3.96  tff(c_30, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.08/3.96  tff(c_70, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.08/3.96  tff(c_75, plain, (![A_50, B_51]: (v1_relat_1(A_50) | ~v1_relat_1(B_51) | ~r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_30, c_70])).
% 11.08/3.96  tff(c_79, plain, (![A_7, B_8]: (v1_relat_1(k3_xboole_0(A_7, B_8)) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_20, c_75])).
% 11.08/3.96  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.08/3.96  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.08/3.96  tff(c_34, plain, (![C_27, A_21, B_25]: (r1_tarski(k5_relat_1(C_27, A_21), k5_relat_1(C_27, B_25)) | ~r1_tarski(A_21, B_25) | ~v1_relat_1(C_27) | ~v1_relat_1(B_25) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.08/3.96  tff(c_90, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k3_xboole_0(B_58, C_59)) | ~r1_tarski(A_57, C_59) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.08/3.96  tff(c_36, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.08/3.96  tff(c_98, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_36])).
% 11.08/3.96  tff(c_129, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_98])).
% 11.08/3.96  tff(c_132, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_129])).
% 11.08/3.96  tff(c_135, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_20, c_132])).
% 11.08/3.96  tff(c_138, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_79, c_135])).
% 11.08/3.96  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_138])).
% 11.08/3.96  tff(c_143, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_98])).
% 11.08/3.96  tff(c_147, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_143])).
% 11.08/3.96  tff(c_150, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_147])).
% 11.08/3.96  tff(c_155, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_150])).
% 11.08/3.96  tff(c_179, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_79, c_155])).
% 11.08/3.96  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_179])).
% 11.08/3.96  tff(c_184, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_150])).
% 11.08/3.96  tff(c_13146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12716, c_184])).
% 11.08/3.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.08/3.96  
% 11.08/3.96  Inference rules
% 11.08/3.96  ----------------------
% 11.08/3.96  #Ref     : 0
% 11.08/3.96  #Sup     : 2832
% 11.08/3.96  #Fact    : 0
% 11.08/3.96  #Define  : 0
% 11.08/3.96  #Split   : 3
% 11.08/3.96  #Chain   : 0
% 11.08/3.97  #Close   : 0
% 11.08/3.97  
% 11.08/3.97  Ordering : KBO
% 11.08/3.97  
% 11.08/3.97  Simplification rules
% 11.08/3.97  ----------------------
% 11.08/3.97  #Subsume      : 1577
% 11.08/3.97  #Demod        : 3657
% 11.08/3.97  #Tautology    : 301
% 11.08/3.97  #SimpNegUnit  : 0
% 11.08/3.97  #BackRed      : 5
% 11.08/3.97  
% 11.08/3.97  #Partial instantiations: 0
% 11.08/3.97  #Strategies tried      : 1
% 11.08/3.97  
% 11.08/3.97  Timing (in seconds)
% 11.08/3.97  ----------------------
% 11.08/3.97  Preprocessing        : 0.33
% 11.08/3.97  Parsing              : 0.17
% 11.08/3.97  CNF conversion       : 0.03
% 11.08/3.97  Main loop            : 2.82
% 11.08/3.97  Inferencing          : 0.95
% 11.08/3.97  Reduction            : 0.65
% 11.08/3.97  Demodulation         : 0.47
% 11.08/3.97  BG Simplification    : 0.08
% 11.08/3.97  Subsumption          : 1.01
% 11.08/3.97  Abstraction          : 0.22
% 11.08/3.97  MUC search           : 0.00
% 11.08/3.97  Cooper               : 0.00
% 11.08/3.97  Total                : 3.19
% 11.08/3.97  Index Insertion      : 0.00
% 11.08/3.97  Index Deletion       : 0.00
% 11.08/3.97  Index Matching       : 0.00
% 11.08/3.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
