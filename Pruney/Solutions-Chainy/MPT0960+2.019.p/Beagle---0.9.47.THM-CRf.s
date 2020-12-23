%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:39 EST 2020

% Result     : Theorem 48.42s
% Output     : CNFRefutation 48.42s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 131 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 205 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_42,plain,(
    ! [A_26] : v1_relat_1(k1_wellord2(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_18] :
      ( k3_relat_1(k1_wellord2(A_18)) = A_18
      | ~ v1_relat_1(k1_wellord2(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    ! [A_18] : k3_relat_1(k1_wellord2(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_189,plain,(
    ! [A_48] :
      ( k2_xboole_0(k1_relat_1(A_48),k2_relat_1(A_48)) = k3_relat_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_213,plain,(
    ! [A_49] :
      ( r1_tarski(k1_relat_1(A_49),k3_relat_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_14])).

tff(c_221,plain,(
    ! [A_18] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_18)),A_18)
      | ~ v1_relat_1(k1_wellord2(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_213])).

tff(c_225,plain,(
    ! [A_18] : r1_tarski(k1_relat_1(k1_wellord2(A_18)),A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_221])).

tff(c_303,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(k2_zfmisc_1(A_56,C_57),k2_zfmisc_1(B_58,C_57))
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_310,plain,(
    ! [A_56,C_57,B_58] :
      ( k2_xboole_0(k2_zfmisc_1(A_56,C_57),k2_zfmisc_1(B_58,C_57)) = k2_zfmisc_1(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(resolution,[status(thm)],[c_303,c_12])).

tff(c_226,plain,(
    ! [A_50] : r1_tarski(k1_relat_1(k1_wellord2(A_50)),A_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_221])).

tff(c_233,plain,(
    ! [A_50] : k2_xboole_0(k1_relat_1(k1_wellord2(A_50)),A_50) = A_50 ),
    inference(resolution,[status(thm)],[c_226,c_12])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_14,c_64])).

tff(c_18320,plain,(
    ! [A_426] :
      ( k2_xboole_0(k1_relat_1(A_426),k3_relat_1(A_426)) = k2_xboole_0(k1_relat_1(A_426),k2_relat_1(A_426))
      | ~ v1_relat_1(A_426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_71])).

tff(c_18571,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(k1_wellord2(A_18)),k2_relat_1(k1_wellord2(A_18))) = k2_xboole_0(k1_relat_1(k1_wellord2(A_18)),A_18)
      | ~ v1_relat_1(k1_wellord2(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_18320])).

tff(c_18605,plain,(
    ! [A_18] : k2_xboole_0(k1_relat_1(k1_wellord2(A_18)),k2_relat_1(k1_wellord2(A_18))) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_233,c_18571])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_133,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,k2_xboole_0(C_44,B_45))
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_736,plain,(
    ! [A_88,C_89,B_90,B_91] :
      ( r1_tarski(A_88,k2_xboole_0(C_89,B_90))
      | ~ r1_tarski(k2_xboole_0(A_88,B_91),B_90) ) ),
    inference(resolution,[status(thm)],[c_133,c_10])).

tff(c_775,plain,(
    ! [A_92,C_93,B_94] : r1_tarski(A_92,k2_xboole_0(C_93,k2_xboole_0(A_92,B_94))) ),
    inference(resolution,[status(thm)],[c_6,c_736])).

tff(c_823,plain,(
    ! [B_2,C_93] : r1_tarski(B_2,k2_xboole_0(C_93,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_775])).

tff(c_431,plain,(
    ! [C_67,A_68,B_69] :
      ( r1_tarski(k2_zfmisc_1(C_67,A_68),k2_zfmisc_1(C_67,B_69))
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_438,plain,(
    ! [C_67,A_68,B_69] :
      ( k2_xboole_0(k2_zfmisc_1(C_67,A_68),k2_zfmisc_1(C_67,B_69)) = k2_zfmisc_1(C_67,B_69)
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_431,c_12])).

tff(c_4130,plain,(
    ! [C_194,A_195,B_196] :
      ( k2_xboole_0(k2_zfmisc_1(C_194,A_195),k2_zfmisc_1(C_194,B_196)) = k2_zfmisc_1(C_194,B_196)
      | ~ r1_tarski(A_195,B_196) ) ),
    inference(resolution,[status(thm)],[c_431,c_12])).

tff(c_86,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(k2_xboole_0(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [A_35,B_37,B_12] : r1_tarski(A_35,k2_xboole_0(k2_xboole_0(A_35,B_37),B_12)) ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_13289,plain,(
    ! [C_374,A_375,B_376,B_377] :
      ( r1_tarski(k2_zfmisc_1(C_374,A_375),k2_xboole_0(k2_zfmisc_1(C_374,B_376),B_377))
      | ~ r1_tarski(A_375,B_376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4130,c_98])).

tff(c_86028,plain,(
    ! [C_1122,A_1123,B_1124,A_1125] :
      ( r1_tarski(k2_zfmisc_1(C_1122,A_1123),k2_zfmisc_1(C_1122,B_1124))
      | ~ r1_tarski(A_1123,A_1125)
      | ~ r1_tarski(A_1125,B_1124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_13289])).

tff(c_86743,plain,(
    ! [C_1126,B_1127,B_1128,C_1129] :
      ( r1_tarski(k2_zfmisc_1(C_1126,B_1127),k2_zfmisc_1(C_1126,B_1128))
      | ~ r1_tarski(k2_xboole_0(C_1129,B_1127),B_1128) ) ),
    inference(resolution,[status(thm)],[c_823,c_86028])).

tff(c_87106,plain,(
    ! [C_1130,B_1131,C_1132] : r1_tarski(k2_zfmisc_1(C_1130,B_1131),k2_zfmisc_1(C_1130,k2_xboole_0(C_1132,B_1131))) ),
    inference(resolution,[status(thm)],[c_6,c_86743])).

tff(c_87368,plain,(
    ! [C_1133,A_1134] : r1_tarski(k2_zfmisc_1(C_1133,k2_relat_1(k1_wellord2(A_1134))),k2_zfmisc_1(C_1133,A_1134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18605,c_87106])).

tff(c_134548,plain,(
    ! [C_1510,A_1511] : k2_xboole_0(k2_zfmisc_1(C_1510,k2_relat_1(k1_wellord2(A_1511))),k2_zfmisc_1(C_1510,A_1511)) = k2_zfmisc_1(C_1510,A_1511) ),
    inference(resolution,[status(thm)],[c_87368,c_12])).

tff(c_234,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,k2_zfmisc_1(k1_relat_1(A_51),k2_relat_1(A_51)))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5100,plain,(
    ! [A_222] :
      ( k2_xboole_0(A_222,k2_zfmisc_1(k1_relat_1(A_222),k2_relat_1(A_222))) = k2_zfmisc_1(k1_relat_1(A_222),k2_relat_1(A_222))
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_234,c_12])).

tff(c_17373,plain,(
    ! [A_414,C_415] :
      ( r1_tarski(A_414,C_415)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_414),k2_relat_1(A_414)),C_415)
      | ~ v1_relat_1(A_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5100,c_10])).

tff(c_17526,plain,(
    ! [A_414,B_37,B_12] :
      ( r1_tarski(A_414,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(k1_relat_1(A_414),k2_relat_1(A_414)),B_37),B_12))
      | ~ v1_relat_1(A_414) ) ),
    inference(resolution,[status(thm)],[c_98,c_17373])).

tff(c_134677,plain,(
    ! [A_1511,B_12] :
      ( r1_tarski(k1_wellord2(A_1511),k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1511)),A_1511),B_12))
      | ~ v1_relat_1(k1_wellord2(A_1511)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134548,c_17526])).

tff(c_135528,plain,(
    ! [A_1512,B_1513] : r1_tarski(k1_wellord2(A_1512),k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1512)),A_1512),B_1513)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_134677])).

tff(c_136190,plain,(
    ! [C_1526,B_1527] :
      ( r1_tarski(k1_wellord2(C_1526),k2_zfmisc_1(B_1527,C_1526))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(C_1526)),B_1527) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_135528])).

tff(c_136870,plain,(
    ! [A_18] : r1_tarski(k1_wellord2(A_18),k2_zfmisc_1(A_18,A_18)) ),
    inference(resolution,[status(thm)],[c_225,c_136190])).

tff(c_44,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_137055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136870,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.42/36.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.42/36.95  
% 48.42/36.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.42/36.95  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1
% 48.42/36.95  
% 48.42/36.95  %Foreground sorts:
% 48.42/36.95  
% 48.42/36.95  
% 48.42/36.95  %Background operators:
% 48.42/36.95  
% 48.42/36.95  
% 48.42/36.95  %Foreground operators:
% 48.42/36.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.42/36.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.42/36.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 48.42/36.95  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 48.42/36.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.42/36.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 48.42/36.95  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 48.42/36.95  tff('#skF_3', type, '#skF_3': $i).
% 48.42/36.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.42/36.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.42/36.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.42/36.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.42/36.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 48.42/36.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 48.42/36.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 48.42/36.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.42/36.95  
% 48.42/36.97  tff(f_76, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 48.42/36.97  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 48.42/36.97  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 48.42/36.97  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 48.42/36.97  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 48.42/36.97  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 48.42/36.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 48.42/36.97  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 48.42/36.97  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 48.42/36.97  tff(f_59, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 48.42/36.97  tff(f_79, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 48.42/36.97  tff(c_42, plain, (![A_26]: (v1_relat_1(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 48.42/36.97  tff(c_36, plain, (![A_18]: (k3_relat_1(k1_wellord2(A_18))=A_18 | ~v1_relat_1(k1_wellord2(A_18)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 48.42/36.97  tff(c_50, plain, (![A_18]: (k3_relat_1(k1_wellord2(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 48.42/36.97  tff(c_189, plain, (![A_48]: (k2_xboole_0(k1_relat_1(A_48), k2_relat_1(A_48))=k3_relat_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 48.42/36.97  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 48.42/36.97  tff(c_213, plain, (![A_49]: (r1_tarski(k1_relat_1(A_49), k3_relat_1(A_49)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_189, c_14])).
% 48.42/36.97  tff(c_221, plain, (![A_18]: (r1_tarski(k1_relat_1(k1_wellord2(A_18)), A_18) | ~v1_relat_1(k1_wellord2(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_213])).
% 48.42/36.97  tff(c_225, plain, (![A_18]: (r1_tarski(k1_relat_1(k1_wellord2(A_18)), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_221])).
% 48.42/36.97  tff(c_303, plain, (![A_56, C_57, B_58]: (r1_tarski(k2_zfmisc_1(A_56, C_57), k2_zfmisc_1(B_58, C_57)) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.42/36.97  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 48.42/36.97  tff(c_310, plain, (![A_56, C_57, B_58]: (k2_xboole_0(k2_zfmisc_1(A_56, C_57), k2_zfmisc_1(B_58, C_57))=k2_zfmisc_1(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(resolution, [status(thm)], [c_303, c_12])).
% 48.42/36.97  tff(c_226, plain, (![A_50]: (r1_tarski(k1_relat_1(k1_wellord2(A_50)), A_50))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_221])).
% 48.42/36.97  tff(c_233, plain, (![A_50]: (k2_xboole_0(k1_relat_1(k1_wellord2(A_50)), A_50)=A_50)), inference(resolution, [status(thm)], [c_226, c_12])).
% 48.42/36.97  tff(c_64, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 48.42/36.97  tff(c_71, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_64])).
% 48.42/36.97  tff(c_18320, plain, (![A_426]: (k2_xboole_0(k1_relat_1(A_426), k3_relat_1(A_426))=k2_xboole_0(k1_relat_1(A_426), k2_relat_1(A_426)) | ~v1_relat_1(A_426))), inference(superposition, [status(thm), theory('equality')], [c_189, c_71])).
% 48.42/36.97  tff(c_18571, plain, (![A_18]: (k2_xboole_0(k1_relat_1(k1_wellord2(A_18)), k2_relat_1(k1_wellord2(A_18)))=k2_xboole_0(k1_relat_1(k1_wellord2(A_18)), A_18) | ~v1_relat_1(k1_wellord2(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_18320])).
% 48.42/36.97  tff(c_18605, plain, (![A_18]: (k2_xboole_0(k1_relat_1(k1_wellord2(A_18)), k2_relat_1(k1_wellord2(A_18)))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_233, c_18571])).
% 48.42/36.97  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 48.42/36.97  tff(c_72, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_64])).
% 48.42/36.97  tff(c_133, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, k2_xboole_0(C_44, B_45)) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 48.42/36.97  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 48.42/36.97  tff(c_736, plain, (![A_88, C_89, B_90, B_91]: (r1_tarski(A_88, k2_xboole_0(C_89, B_90)) | ~r1_tarski(k2_xboole_0(A_88, B_91), B_90))), inference(resolution, [status(thm)], [c_133, c_10])).
% 48.42/36.97  tff(c_775, plain, (![A_92, C_93, B_94]: (r1_tarski(A_92, k2_xboole_0(C_93, k2_xboole_0(A_92, B_94))))), inference(resolution, [status(thm)], [c_6, c_736])).
% 48.42/36.97  tff(c_823, plain, (![B_2, C_93]: (r1_tarski(B_2, k2_xboole_0(C_93, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_775])).
% 48.42/36.97  tff(c_431, plain, (![C_67, A_68, B_69]: (r1_tarski(k2_zfmisc_1(C_67, A_68), k2_zfmisc_1(C_67, B_69)) | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 48.42/36.97  tff(c_438, plain, (![C_67, A_68, B_69]: (k2_xboole_0(k2_zfmisc_1(C_67, A_68), k2_zfmisc_1(C_67, B_69))=k2_zfmisc_1(C_67, B_69) | ~r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_431, c_12])).
% 48.42/36.97  tff(c_4130, plain, (![C_194, A_195, B_196]: (k2_xboole_0(k2_zfmisc_1(C_194, A_195), k2_zfmisc_1(C_194, B_196))=k2_zfmisc_1(C_194, B_196) | ~r1_tarski(A_195, B_196))), inference(resolution, [status(thm)], [c_431, c_12])).
% 48.42/36.97  tff(c_86, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(k2_xboole_0(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 48.42/36.97  tff(c_98, plain, (![A_35, B_37, B_12]: (r1_tarski(A_35, k2_xboole_0(k2_xboole_0(A_35, B_37), B_12)))), inference(resolution, [status(thm)], [c_14, c_86])).
% 48.42/36.97  tff(c_13289, plain, (![C_374, A_375, B_376, B_377]: (r1_tarski(k2_zfmisc_1(C_374, A_375), k2_xboole_0(k2_zfmisc_1(C_374, B_376), B_377)) | ~r1_tarski(A_375, B_376))), inference(superposition, [status(thm), theory('equality')], [c_4130, c_98])).
% 48.42/36.97  tff(c_86028, plain, (![C_1122, A_1123, B_1124, A_1125]: (r1_tarski(k2_zfmisc_1(C_1122, A_1123), k2_zfmisc_1(C_1122, B_1124)) | ~r1_tarski(A_1123, A_1125) | ~r1_tarski(A_1125, B_1124))), inference(superposition, [status(thm), theory('equality')], [c_438, c_13289])).
% 48.42/36.97  tff(c_86743, plain, (![C_1126, B_1127, B_1128, C_1129]: (r1_tarski(k2_zfmisc_1(C_1126, B_1127), k2_zfmisc_1(C_1126, B_1128)) | ~r1_tarski(k2_xboole_0(C_1129, B_1127), B_1128))), inference(resolution, [status(thm)], [c_823, c_86028])).
% 48.42/36.97  tff(c_87106, plain, (![C_1130, B_1131, C_1132]: (r1_tarski(k2_zfmisc_1(C_1130, B_1131), k2_zfmisc_1(C_1130, k2_xboole_0(C_1132, B_1131))))), inference(resolution, [status(thm)], [c_6, c_86743])).
% 48.42/36.97  tff(c_87368, plain, (![C_1133, A_1134]: (r1_tarski(k2_zfmisc_1(C_1133, k2_relat_1(k1_wellord2(A_1134))), k2_zfmisc_1(C_1133, A_1134)))), inference(superposition, [status(thm), theory('equality')], [c_18605, c_87106])).
% 48.42/36.97  tff(c_134548, plain, (![C_1510, A_1511]: (k2_xboole_0(k2_zfmisc_1(C_1510, k2_relat_1(k1_wellord2(A_1511))), k2_zfmisc_1(C_1510, A_1511))=k2_zfmisc_1(C_1510, A_1511))), inference(resolution, [status(thm)], [c_87368, c_12])).
% 48.42/36.97  tff(c_234, plain, (![A_51]: (r1_tarski(A_51, k2_zfmisc_1(k1_relat_1(A_51), k2_relat_1(A_51))) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 48.42/36.97  tff(c_5100, plain, (![A_222]: (k2_xboole_0(A_222, k2_zfmisc_1(k1_relat_1(A_222), k2_relat_1(A_222)))=k2_zfmisc_1(k1_relat_1(A_222), k2_relat_1(A_222)) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_234, c_12])).
% 48.42/36.97  tff(c_17373, plain, (![A_414, C_415]: (r1_tarski(A_414, C_415) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_414), k2_relat_1(A_414)), C_415) | ~v1_relat_1(A_414))), inference(superposition, [status(thm), theory('equality')], [c_5100, c_10])).
% 48.42/36.97  tff(c_17526, plain, (![A_414, B_37, B_12]: (r1_tarski(A_414, k2_xboole_0(k2_xboole_0(k2_zfmisc_1(k1_relat_1(A_414), k2_relat_1(A_414)), B_37), B_12)) | ~v1_relat_1(A_414))), inference(resolution, [status(thm)], [c_98, c_17373])).
% 48.42/36.97  tff(c_134677, plain, (![A_1511, B_12]: (r1_tarski(k1_wellord2(A_1511), k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1511)), A_1511), B_12)) | ~v1_relat_1(k1_wellord2(A_1511)))), inference(superposition, [status(thm), theory('equality')], [c_134548, c_17526])).
% 48.42/36.97  tff(c_135528, plain, (![A_1512, B_1513]: (r1_tarski(k1_wellord2(A_1512), k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1512)), A_1512), B_1513)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_134677])).
% 48.42/36.97  tff(c_136190, plain, (![C_1526, B_1527]: (r1_tarski(k1_wellord2(C_1526), k2_zfmisc_1(B_1527, C_1526)) | ~r1_tarski(k1_relat_1(k1_wellord2(C_1526)), B_1527))), inference(superposition, [status(thm), theory('equality')], [c_310, c_135528])).
% 48.42/36.97  tff(c_136870, plain, (![A_18]: (r1_tarski(k1_wellord2(A_18), k2_zfmisc_1(A_18, A_18)))), inference(resolution, [status(thm)], [c_225, c_136190])).
% 48.42/36.97  tff(c_44, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 48.42/36.97  tff(c_137055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136870, c_44])).
% 48.42/36.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.42/36.97  
% 48.42/36.97  Inference rules
% 48.42/36.97  ----------------------
% 48.42/36.97  #Ref     : 0
% 48.42/36.97  #Sup     : 36286
% 48.42/36.97  #Fact    : 0
% 48.42/36.97  #Define  : 0
% 48.42/36.97  #Split   : 0
% 48.42/36.97  #Chain   : 0
% 48.42/36.97  #Close   : 0
% 48.42/36.97  
% 48.42/36.97  Ordering : KBO
% 48.42/36.97  
% 48.42/36.97  Simplification rules
% 48.42/36.97  ----------------------
% 48.42/36.97  #Subsume      : 5420
% 48.42/36.97  #Demod        : 11542
% 48.42/36.97  #Tautology    : 8090
% 48.42/36.97  #SimpNegUnit  : 0
% 48.42/36.97  #BackRed      : 1
% 48.42/36.97  
% 48.42/36.97  #Partial instantiations: 0
% 48.42/36.97  #Strategies tried      : 1
% 48.42/36.97  
% 48.42/36.97  Timing (in seconds)
% 48.42/36.97  ----------------------
% 48.42/36.97  Preprocessing        : 0.31
% 48.42/36.97  Parsing              : 0.16
% 48.42/36.97  CNF conversion       : 0.02
% 48.42/36.97  Main loop            : 35.91
% 48.42/36.97  Inferencing          : 3.06
% 48.42/36.97  Reduction            : 15.48
% 48.42/36.97  Demodulation         : 14.04
% 48.42/36.97  BG Simplification    : 0.56
% 48.42/36.97  Subsumption          : 14.91
% 48.42/36.97  Abstraction          : 0.77
% 48.42/36.97  MUC search           : 0.00
% 48.42/36.97  Cooper               : 0.00
% 48.42/36.97  Total                : 36.25
% 48.42/36.97  Index Insertion      : 0.00
% 48.42/36.97  Index Deletion       : 0.00
% 48.42/36.97  Index Matching       : 0.00
% 48.42/36.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
