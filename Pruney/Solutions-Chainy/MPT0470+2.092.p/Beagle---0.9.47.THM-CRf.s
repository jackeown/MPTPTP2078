%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 567 expanded)
%              Number of leaves         :   32 ( 195 expanded)
%              Depth                    :   21
%              Number of atoms          :  198 (1236 expanded)
%              Number of equality atoms :   37 ( 107 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_99,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_44,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_85,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_2'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_43,B_44] :
      ( ~ v1_xboole_0(A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_141,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_146,plain,(
    ! [A_57,B_58] :
      ( v1_relat_1(A_57)
      | ~ v1_relat_1(B_58)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_153,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(A_43)
      | ~ v1_relat_1(B_44)
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_108,c_146])).

tff(c_155,plain,(
    ! [B_44] : ~ v1_relat_1(B_44) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_46])).

tff(c_170,plain,(
    ! [A_62] :
      ( v1_relat_1(A_62)
      | ~ v1_xboole_0(A_62) ) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_174,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_170])).

tff(c_28,plain,(
    ! [A_18] :
      ( v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k5_relat_1(A_19,B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_199,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_70,B_71)),k2_relat_1(B_71))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_213,plain,(
    ! [A_70] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_70,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_199])).

tff(c_220,plain,(
    ! [A_72] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_72,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_213])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_182,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66),B_67)
      | ~ r1_tarski(A_66,B_67)
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_4,c_175])).

tff(c_189,plain,(
    ! [B_67,A_66] :
      ( ~ v1_xboole_0(B_67)
      | ~ r1_tarski(A_66,B_67)
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_223,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k2_relat_1(k5_relat_1(A_72,k1_xboole_0)))
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_220,c_189])).

tff(c_242,plain,(
    ! [A_73] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_73,k1_xboole_0)))
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_223])).

tff(c_32,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k2_relat_1(A_21))
      | ~ v1_relat_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_314,plain,(
    ! [A_78] :
      ( ~ v1_relat_1(k5_relat_1(A_78,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_78,k1_xboole_0))
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_242,c_32])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_336,plain,(
    ! [A_81] :
      ( k5_relat_1(A_81,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_81,k1_xboole_0))
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_314,c_14])).

tff(c_340,plain,(
    ! [A_19] :
      ( k5_relat_1(A_19,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_30,c_336])).

tff(c_344,plain,(
    ! [A_82] :
      ( k5_relat_1(A_82,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_340])).

tff(c_363,plain,(
    ! [A_18] :
      ( k5_relat_1(k4_relat_1(A_18),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_344])).

tff(c_34,plain,(
    ! [A_22] :
      ( k4_relat_1(k4_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_258,plain,(
    ! [B_74,A_75] :
      ( k5_relat_1(k4_relat_1(B_74),k4_relat_1(A_75)) = k4_relat_1(k5_relat_1(A_75,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_868,plain,(
    ! [A_107,B_108] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_107),B_108)) = k5_relat_1(k4_relat_1(B_108),A_107)
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(k4_relat_1(A_107))
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_258])).

tff(c_901,plain,(
    ! [A_18] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_18) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_868])).

tff(c_912,plain,(
    ! [A_109] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_109) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_109))
      | ~ v1_relat_1(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_901])).

tff(c_927,plain,(
    ! [A_110] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_110) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_28,c_912])).

tff(c_954,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_363])).

tff(c_1000,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_174,c_954])).

tff(c_926,plain,(
    ! [A_18] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_18) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_912])).

tff(c_1104,plain,(
    ! [A_113] :
      ( k5_relat_1(k1_xboole_0,A_113) = k1_xboole_0
      | ~ v1_relat_1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1000,c_926])).

tff(c_1125,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1104])).

tff(c_1136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1125])).

tff(c_1137,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1177,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_2'(A_128,B_129),A_128)
      | r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1188,plain,(
    ! [A_130,B_131] :
      ( ~ v1_xboole_0(A_130)
      | r1_tarski(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_1177,c_2])).

tff(c_1160,plain,(
    ! [B_120,A_121] :
      ( v1_relat_1(B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_121))
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1164,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(A_13)
      | ~ v1_relat_1(B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_1160])).

tff(c_1192,plain,(
    ! [A_130,B_131] :
      ( v1_relat_1(A_130)
      | ~ v1_relat_1(B_131)
      | ~ v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_1188,c_1164])).

tff(c_1193,plain,(
    ! [B_131] : ~ v1_relat_1(B_131) ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_1209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1193,c_46])).

tff(c_1211,plain,(
    ! [A_134] :
      ( v1_relat_1(A_134)
      | ~ v1_xboole_0(A_134) ) ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_1215,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_1211])).

tff(c_1264,plain,(
    ! [A_148,B_149] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_148,B_149)),k2_relat_1(B_149))
      | ~ v1_relat_1(B_149)
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1281,plain,(
    ! [A_148] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_148,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1264])).

tff(c_1312,plain,(
    ! [A_150] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_150,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1281])).

tff(c_1187,plain,(
    ! [A_128,B_129] :
      ( ~ v1_xboole_0(A_128)
      | r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_1177,c_2])).

tff(c_1216,plain,(
    ! [B_135,A_136] :
      ( B_135 = A_136
      | ~ r1_tarski(B_135,A_136)
      | ~ r1_tarski(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1221,plain,(
    ! [B_129,A_128] :
      ( B_129 = A_128
      | ~ r1_tarski(B_129,A_128)
      | ~ v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_1187,c_1216])).

tff(c_1318,plain,(
    ! [A_150] :
      ( k2_relat_1(k5_relat_1(A_150,k1_xboole_0)) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_1312,c_1221])).

tff(c_1350,plain,(
    ! [A_152] :
      ( k2_relat_1(k5_relat_1(A_152,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1318])).

tff(c_1368,plain,(
    ! [A_152] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_152,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_152,k1_xboole_0))
      | ~ v1_relat_1(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_32])).

tff(c_1413,plain,(
    ! [A_158] :
      ( ~ v1_relat_1(k5_relat_1(A_158,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_158,k1_xboole_0))
      | ~ v1_relat_1(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1368])).

tff(c_1428,plain,(
    ! [A_159] :
      ( k5_relat_1(A_159,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_159,k1_xboole_0))
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_1413,c_14])).

tff(c_1432,plain,(
    ! [A_19] :
      ( k5_relat_1(A_19,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_30,c_1428])).

tff(c_1436,plain,(
    ! [A_160] :
      ( k5_relat_1(A_160,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1432])).

tff(c_1451,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1436])).

tff(c_1459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1137,c_1451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:21:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.46  
% 3.32/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.32/1.47  
% 3.32/1.47  %Foreground sorts:
% 3.32/1.47  
% 3.32/1.47  
% 3.32/1.47  %Background operators:
% 3.32/1.47  
% 3.32/1.47  
% 3.32/1.47  %Foreground operators:
% 3.32/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.32/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.47  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.32/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.47  
% 3.32/1.49  tff(f_106, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.32/1.49  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.32/1.49  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.32/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.32/1.49  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.49  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.32/1.49  tff(f_64, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.32/1.49  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.32/1.49  tff(f_99, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.32/1.49  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.32/1.49  tff(f_78, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.32/1.49  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.32/1.49  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.32/1.49  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.32/1.49  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.49  tff(c_44, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_85, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.32/1.49  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.32/1.49  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.49  tff(c_104, plain, (![A_43, B_44]: (r2_hidden('#skF_2'(A_43, B_44), A_43) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.49  tff(c_108, plain, (![A_43, B_44]: (~v1_xboole_0(A_43) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_104, c_2])).
% 3.32/1.49  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.49  tff(c_141, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.32/1.49  tff(c_146, plain, (![A_57, B_58]: (v1_relat_1(A_57) | ~v1_relat_1(B_58) | ~r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_24, c_141])).
% 3.32/1.49  tff(c_153, plain, (![A_43, B_44]: (v1_relat_1(A_43) | ~v1_relat_1(B_44) | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_108, c_146])).
% 3.32/1.49  tff(c_155, plain, (![B_44]: (~v1_relat_1(B_44))), inference(splitLeft, [status(thm)], [c_153])).
% 3.32/1.49  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_46])).
% 3.32/1.49  tff(c_170, plain, (![A_62]: (v1_relat_1(A_62) | ~v1_xboole_0(A_62))), inference(splitRight, [status(thm)], [c_153])).
% 3.32/1.49  tff(c_174, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_170])).
% 3.32/1.49  tff(c_28, plain, (![A_18]: (v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.49  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k5_relat_1(A_19, B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.32/1.49  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.32/1.49  tff(c_199, plain, (![A_70, B_71]: (r1_tarski(k2_relat_1(k5_relat_1(A_70, B_71)), k2_relat_1(B_71)) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.32/1.49  tff(c_213, plain, (![A_70]: (r1_tarski(k2_relat_1(k5_relat_1(A_70, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_40, c_199])).
% 3.32/1.49  tff(c_220, plain, (![A_72]: (r1_tarski(k2_relat_1(k5_relat_1(A_72, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_213])).
% 3.32/1.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.49  tff(c_175, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.49  tff(c_182, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66), B_67) | ~r1_tarski(A_66, B_67) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_4, c_175])).
% 3.32/1.49  tff(c_189, plain, (![B_67, A_66]: (~v1_xboole_0(B_67) | ~r1_tarski(A_66, B_67) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_182, c_2])).
% 3.32/1.49  tff(c_223, plain, (![A_72]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_relat_1(k5_relat_1(A_72, k1_xboole_0))) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_220, c_189])).
% 3.32/1.49  tff(c_242, plain, (![A_73]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_73, k1_xboole_0))) | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_223])).
% 3.32/1.49  tff(c_32, plain, (![A_21]: (~v1_xboole_0(k2_relat_1(A_21)) | ~v1_relat_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.32/1.49  tff(c_314, plain, (![A_78]: (~v1_relat_1(k5_relat_1(A_78, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_78, k1_xboole_0)) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_242, c_32])).
% 3.32/1.49  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.49  tff(c_336, plain, (![A_81]: (k5_relat_1(A_81, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_81, k1_xboole_0)) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_314, c_14])).
% 3.32/1.49  tff(c_340, plain, (![A_19]: (k5_relat_1(A_19, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_30, c_336])).
% 3.32/1.49  tff(c_344, plain, (![A_82]: (k5_relat_1(A_82, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_340])).
% 3.32/1.49  tff(c_363, plain, (![A_18]: (k5_relat_1(k4_relat_1(A_18), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_28, c_344])).
% 3.32/1.49  tff(c_34, plain, (![A_22]: (k4_relat_1(k4_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.32/1.49  tff(c_258, plain, (![B_74, A_75]: (k5_relat_1(k4_relat_1(B_74), k4_relat_1(A_75))=k4_relat_1(k5_relat_1(A_75, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.49  tff(c_868, plain, (![A_107, B_108]: (k4_relat_1(k5_relat_1(k4_relat_1(A_107), B_108))=k5_relat_1(k4_relat_1(B_108), A_107) | ~v1_relat_1(B_108) | ~v1_relat_1(k4_relat_1(A_107)) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_34, c_258])).
% 3.32/1.49  tff(c_901, plain, (![A_18]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_18)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_363, c_868])).
% 3.32/1.49  tff(c_912, plain, (![A_109]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_109)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_109)) | ~v1_relat_1(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_901])).
% 3.32/1.49  tff(c_927, plain, (![A_110]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_110)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_28, c_912])).
% 3.32/1.49  tff(c_954, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_927, c_363])).
% 3.32/1.49  tff(c_1000, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_174, c_174, c_954])).
% 3.32/1.49  tff(c_926, plain, (![A_18]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_18)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_28, c_912])).
% 3.32/1.49  tff(c_1104, plain, (![A_113]: (k5_relat_1(k1_xboole_0, A_113)=k1_xboole_0 | ~v1_relat_1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1000, c_926])).
% 3.32/1.49  tff(c_1125, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1104])).
% 3.32/1.49  tff(c_1136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_1125])).
% 3.32/1.49  tff(c_1137, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.32/1.49  tff(c_1177, plain, (![A_128, B_129]: (r2_hidden('#skF_2'(A_128, B_129), A_128) | r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.49  tff(c_1188, plain, (![A_130, B_131]: (~v1_xboole_0(A_130) | r1_tarski(A_130, B_131))), inference(resolution, [status(thm)], [c_1177, c_2])).
% 3.32/1.49  tff(c_1160, plain, (![B_120, A_121]: (v1_relat_1(B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_121)) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.32/1.49  tff(c_1164, plain, (![A_13, B_14]: (v1_relat_1(A_13) | ~v1_relat_1(B_14) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_24, c_1160])).
% 3.32/1.49  tff(c_1192, plain, (![A_130, B_131]: (v1_relat_1(A_130) | ~v1_relat_1(B_131) | ~v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_1188, c_1164])).
% 3.32/1.49  tff(c_1193, plain, (![B_131]: (~v1_relat_1(B_131))), inference(splitLeft, [status(thm)], [c_1192])).
% 3.32/1.49  tff(c_1209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1193, c_46])).
% 3.32/1.49  tff(c_1211, plain, (![A_134]: (v1_relat_1(A_134) | ~v1_xboole_0(A_134))), inference(splitRight, [status(thm)], [c_1192])).
% 3.32/1.49  tff(c_1215, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1211])).
% 3.32/1.49  tff(c_1264, plain, (![A_148, B_149]: (r1_tarski(k2_relat_1(k5_relat_1(A_148, B_149)), k2_relat_1(B_149)) | ~v1_relat_1(B_149) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.32/1.49  tff(c_1281, plain, (![A_148]: (r1_tarski(k2_relat_1(k5_relat_1(A_148, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_148))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1264])).
% 3.32/1.49  tff(c_1312, plain, (![A_150]: (r1_tarski(k2_relat_1(k5_relat_1(A_150, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1281])).
% 3.32/1.49  tff(c_1187, plain, (![A_128, B_129]: (~v1_xboole_0(A_128) | r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_1177, c_2])).
% 3.32/1.49  tff(c_1216, plain, (![B_135, A_136]: (B_135=A_136 | ~r1_tarski(B_135, A_136) | ~r1_tarski(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.49  tff(c_1221, plain, (![B_129, A_128]: (B_129=A_128 | ~r1_tarski(B_129, A_128) | ~v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_1187, c_1216])).
% 3.32/1.49  tff(c_1318, plain, (![A_150]: (k2_relat_1(k5_relat_1(A_150, k1_xboole_0))=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_1312, c_1221])).
% 3.32/1.49  tff(c_1350, plain, (![A_152]: (k2_relat_1(k5_relat_1(A_152, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1318])).
% 3.32/1.49  tff(c_1368, plain, (![A_152]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_152, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_152, k1_xboole_0)) | ~v1_relat_1(A_152))), inference(superposition, [status(thm), theory('equality')], [c_1350, c_32])).
% 3.32/1.49  tff(c_1413, plain, (![A_158]: (~v1_relat_1(k5_relat_1(A_158, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_158, k1_xboole_0)) | ~v1_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1368])).
% 3.32/1.49  tff(c_1428, plain, (![A_159]: (k5_relat_1(A_159, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_159, k1_xboole_0)) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_1413, c_14])).
% 3.32/1.49  tff(c_1432, plain, (![A_19]: (k5_relat_1(A_19, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_30, c_1428])).
% 3.32/1.49  tff(c_1436, plain, (![A_160]: (k5_relat_1(A_160, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1432])).
% 3.32/1.49  tff(c_1451, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1436])).
% 3.32/1.49  tff(c_1459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1137, c_1451])).
% 3.32/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.49  
% 3.32/1.49  Inference rules
% 3.32/1.49  ----------------------
% 3.32/1.49  #Ref     : 0
% 3.32/1.49  #Sup     : 314
% 3.32/1.49  #Fact    : 0
% 3.32/1.49  #Define  : 0
% 3.32/1.49  #Split   : 5
% 3.32/1.49  #Chain   : 0
% 3.32/1.49  #Close   : 0
% 3.32/1.49  
% 3.32/1.49  Ordering : KBO
% 3.32/1.49  
% 3.32/1.49  Simplification rules
% 3.32/1.49  ----------------------
% 3.32/1.49  #Subsume      : 56
% 3.32/1.49  #Demod        : 259
% 3.32/1.49  #Tautology    : 152
% 3.32/1.49  #SimpNegUnit  : 21
% 3.32/1.49  #BackRed      : 10
% 3.32/1.49  
% 3.32/1.49  #Partial instantiations: 0
% 3.32/1.49  #Strategies tried      : 1
% 3.32/1.49  
% 3.32/1.49  Timing (in seconds)
% 3.32/1.49  ----------------------
% 3.32/1.49  Preprocessing        : 0.29
% 3.32/1.49  Parsing              : 0.16
% 3.32/1.49  CNF conversion       : 0.02
% 3.32/1.49  Main loop            : 0.45
% 3.32/1.49  Inferencing          : 0.17
% 3.32/1.49  Reduction            : 0.12
% 3.32/1.49  Demodulation         : 0.08
% 3.32/1.49  BG Simplification    : 0.02
% 3.32/1.49  Subsumption          : 0.10
% 3.32/1.49  Abstraction          : 0.02
% 3.32/1.49  MUC search           : 0.00
% 3.32/1.49  Cooper               : 0.00
% 3.32/1.49  Total                : 0.79
% 3.32/1.49  Index Insertion      : 0.00
% 3.32/1.49  Index Deletion       : 0.00
% 3.32/1.49  Index Matching       : 0.00
% 3.32/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
