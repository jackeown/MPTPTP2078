%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:00 EST 2020

% Result     : Timeout 59.61s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  135 ( 914 expanded)
%              Number of leaves         :   31 ( 337 expanded)
%              Depth                    :   31
%              Number of atoms          :  286 (2011 expanded)
%              Number of equality atoms :   81 ( 545 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [B_39] : k4_xboole_0(B_39,B_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [B_39] : r1_tarski(k1_xboole_0,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_16])).

tff(c_88,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_22,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k9_relat_1(C_25,A_23),k9_relat_1(C_25,B_24)) = k9_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v2_funct_1(C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1252,plain,(
    ! [C_124,A_125,B_126] :
      ( k4_xboole_0(k9_relat_1(C_124,A_125),k9_relat_1(C_124,B_126)) = k9_relat_1(C_124,k4_xboole_0(A_125,B_126))
      | ~ v2_funct_1(C_124)
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_30])).

tff(c_1300,plain,(
    ! [C_124,B_126] :
      ( k9_relat_1(C_124,k4_xboole_0(B_126,B_126)) = k1_xboole_0
      | ~ v2_funct_1(C_124)
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_88])).

tff(c_1322,plain,(
    ! [C_127] :
      ( k9_relat_1(C_127,k1_xboole_0) = k1_xboole_0
      | ~ v2_funct_1(C_127)
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1300])).

tff(c_1325,plain,
    ( k9_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1322])).

tff(c_1328,plain,(
    k9_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1325])).

tff(c_43,plain,(
    ! [C_25,A_23,B_24] :
      ( k4_xboole_0(k9_relat_1(C_25,A_23),k9_relat_1(C_25,B_24)) = k9_relat_1(C_25,k4_xboole_0(A_23,B_24))
      | ~ v2_funct_1(C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_30])).

tff(c_1335,plain,(
    ! [A_23] :
      ( k9_relat_1('#skF_2',k4_xboole_0(A_23,k1_xboole_0)) = k4_xboole_0(k9_relat_1('#skF_2',A_23),k1_xboole_0)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_43])).

tff(c_1344,plain,(
    ! [A_23] : k9_relat_1('#skF_2',k4_xboole_0(A_23,k1_xboole_0)) = k4_xboole_0(k9_relat_1('#skF_2',A_23),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_1335])).

tff(c_8843,plain,(
    ! [C_283,A_284,B_285] :
      ( r1_tarski(k9_relat_1(C_283,k4_xboole_0(A_284,B_285)),k9_relat_1(C_283,A_284))
      | ~ v2_funct_1(C_283)
      | ~ v1_funct_1(C_283)
      | ~ v1_relat_1(C_283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_16])).

tff(c_8934,plain,(
    ! [A_23,B_285] :
      ( r1_tarski(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(A_23,k1_xboole_0),B_285)),k4_xboole_0(k9_relat_1('#skF_2',A_23),k1_xboole_0))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_8843])).

tff(c_42924,plain,(
    ! [A_561,B_562] : r1_tarski(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(A_561,k1_xboole_0),B_562)),k4_xboole_0(k9_relat_1('#skF_2',A_561),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_8934])).

tff(c_289,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_303,plain,(
    ! [A_58,A_10,B_11] :
      ( r1_tarski(A_58,A_10)
      | ~ r1_tarski(A_58,k4_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_43361,plain,(
    ! [A_561,B_562] : r1_tarski(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(A_561,k1_xboole_0),B_562)),k9_relat_1('#skF_2',A_561)) ),
    inference(resolution,[status(thm)],[c_42924,c_303])).

tff(c_50204,plain,(
    ! [A_593,C_594,A_595,B_596] :
      ( r1_tarski(A_593,k9_relat_1(C_594,A_595))
      | ~ r1_tarski(A_593,k9_relat_1(C_594,k4_xboole_0(A_595,B_596)))
      | ~ v2_funct_1(C_594)
      | ~ v1_funct_1(C_594)
      | ~ v1_relat_1(C_594) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_303])).

tff(c_50224,plain,(
    ! [A_595,B_596,B_562] :
      ( r1_tarski(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(k4_xboole_0(A_595,B_596),k1_xboole_0),B_562)),k9_relat_1('#skF_2',A_595))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_43361,c_50204])).

tff(c_191389,plain,(
    ! [A_1222,B_1223,B_1224] : r1_tarski(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(k4_xboole_0(A_1222,B_1223),k1_xboole_0),B_1224)),k9_relat_1('#skF_2',A_1222)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_50224])).

tff(c_325,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k9_relat_1(B_63,k10_relat_1(B_63,A_64)),A_64)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_344,plain,(
    ! [A_7,A_64,B_63] :
      ( r1_tarski(A_7,A_64)
      | ~ r1_tarski(A_7,k9_relat_1(B_63,k10_relat_1(B_63,A_64)))
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_325,c_14])).

tff(c_191414,plain,(
    ! [A_64,B_1223,B_1224] :
      ( r1_tarski(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2',A_64),B_1223),k1_xboole_0),B_1224)),A_64)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_191389,c_344])).

tff(c_195609,plain,(
    ! [A_1233,B_1234,B_1235] : r1_tarski(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2',A_1233),B_1234),k1_xboole_0),B_1235)),A_1233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_191414])).

tff(c_196031,plain,(
    ! [A_1233,B_1234] : r1_tarski(k4_xboole_0(k9_relat_1('#skF_2',k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2',A_1233),B_1234),k1_xboole_0)),k1_xboole_0),A_1233) ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_195609])).

tff(c_196181,plain,(
    ! [A_1233,B_1234] : r1_tarski(k4_xboole_0(k4_xboole_0(k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',A_1233),B_1234)),k1_xboole_0),k1_xboole_0),A_1233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_196031])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( k2_xboole_0(k10_relat_1(C_22,A_20),k10_relat_1(C_22,B_21)) = k10_relat_1(C_22,k2_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26785,plain,(
    ! [C_446,A_447,B_448] :
      ( r1_tarski(k9_relat_1(C_446,k4_xboole_0(k10_relat_1(C_446,A_447),B_448)),A_447)
      | ~ v2_funct_1(C_446)
      | ~ v1_funct_1(C_446)
      | ~ v1_relat_1(C_446) ) ),
    inference(resolution,[status(thm)],[c_8843,c_344])).

tff(c_26889,plain,(
    ! [A_447] :
      ( r1_tarski(k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_447)),k1_xboole_0),A_447)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_26785])).

tff(c_26932,plain,(
    ! [A_449] : r1_tarski(k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_449)),k1_xboole_0),A_449) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_26889])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27063,plain,(
    ! [A_449] : k4_xboole_0(k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_449)),k1_xboole_0),A_449) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26932,c_10])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1032,plain,(
    ! [A_111,B_112,A_113] :
      ( r1_tarski(A_111,B_112)
      | ~ r1_tarski(A_111,A_113)
      | k4_xboole_0(A_113,B_112) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_289])).

tff(c_1064,plain,(
    ! [A_114,B_115,B_116] :
      ( r1_tarski(k4_xboole_0(A_114,B_115),B_116)
      | k4_xboole_0(A_114,B_116) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_1032])).

tff(c_1127,plain,(
    ! [A_114,B_115,B_116] :
      ( k4_xboole_0(k4_xboole_0(A_114,B_115),B_116) = k1_xboole_0
      | k4_xboole_0(A_114,B_116) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1064,c_10])).

tff(c_377,plain,(
    ! [A_67,A_68,B_69] :
      ( r1_tarski(A_67,A_68)
      | ~ r1_tarski(A_67,k4_xboole_0(A_68,B_69)) ) ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_419,plain,(
    ! [A_70,B_71,B_72] : r1_tarski(k4_xboole_0(k4_xboole_0(A_70,B_71),B_72),A_70) ),
    inference(resolution,[status(thm)],[c_16,c_377])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36280,plain,(
    ! [A_502,B_503,B_504] :
      ( k4_xboole_0(k4_xboole_0(A_502,B_503),B_504) = A_502
      | ~ r1_tarski(A_502,k4_xboole_0(k4_xboole_0(A_502,B_503),B_504)) ) ),
    inference(resolution,[status(thm)],[c_419,c_2])).

tff(c_41062,plain,(
    ! [A_549,B_550,B_551] :
      ( k4_xboole_0(k4_xboole_0(A_549,B_550),B_551) = A_549
      | ~ r1_tarski(A_549,k1_xboole_0)
      | k4_xboole_0(A_549,B_551) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_36280])).

tff(c_87,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_47131,plain,(
    ! [A_577,B_578,B_579] :
      ( k4_xboole_0(A_577,k4_xboole_0(A_577,B_578)) = k1_xboole_0
      | ~ r1_tarski(A_577,k1_xboole_0)
      | k4_xboole_0(A_577,B_579) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41062,c_87])).

tff(c_47285,plain,(
    ! [B_580,B_581] :
      ( k4_xboole_0(B_580,k4_xboole_0(B_580,B_581)) = k1_xboole_0
      | ~ r1_tarski(B_580,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_47131])).

tff(c_1059,plain,(
    ! [A_3,B_112,B_4] :
      ( r1_tarski(A_3,B_112)
      | k4_xboole_0(B_4,B_112) != k1_xboole_0
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1032])).

tff(c_49756,plain,(
    ! [A_588,B_589,B_590] :
      ( r1_tarski(A_588,k4_xboole_0(B_589,B_590))
      | k4_xboole_0(A_588,B_589) != k1_xboole_0
      | ~ r1_tarski(B_589,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47285,c_1059])).

tff(c_50019,plain,(
    ! [A_591,B_592] :
      ( r1_tarski(A_591,k1_xboole_0)
      | k4_xboole_0(A_591,B_592) != k1_xboole_0
      | ~ r1_tarski(B_592,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_49756])).

tff(c_90217,plain,(
    ! [A_779] :
      ( r1_tarski(k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_779)),k1_xboole_0),k1_xboole_0)
      | ~ r1_tarski(A_779,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27063,c_50019])).

tff(c_305,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ r1_tarski(A_61,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_94,c_289])).

tff(c_349,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | k4_xboole_0(A_65,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_305])).

tff(c_372,plain,(
    ! [B_66,A_65] :
      ( B_66 = A_65
      | ~ r1_tarski(B_66,A_65)
      | k4_xboole_0(A_65,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_349,c_2])).

tff(c_90239,plain,(
    ! [A_779] :
      ( k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_779)),k1_xboole_0) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
      | ~ r1_tarski(A_779,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_90217,c_372])).

tff(c_90354,plain,(
    ! [A_780] :
      ( k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_780)),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_780,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_90239])).

tff(c_318,plain,(
    ! [A_3,B_62] :
      ( r1_tarski(A_3,B_62)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_305])).

tff(c_245,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_765,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(B_91,A_92)
      | k4_xboole_0(A_92,B_91) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_245])).

tff(c_791,plain,(
    ! [B_62,A_3] :
      ( B_62 = A_3
      | k4_xboole_0(B_62,A_3) != k1_xboole_0
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_318,c_765])).

tff(c_90757,plain,(
    ! [A_780] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_780)) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
      | ~ r1_tarski(A_780,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90354,c_791])).

tff(c_91577,plain,(
    ! [A_784] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_784)) = k1_xboole_0
      | ~ r1_tarski(A_784,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_90757])).

tff(c_91915,plain,(
    ! [A_784,B_24] :
      ( k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',A_784),B_24)) = k4_xboole_0(k1_xboole_0,k9_relat_1('#skF_2',B_24))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_784,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91577,c_43])).

tff(c_92096,plain,(
    ! [A_784,B_24] :
      ( k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',A_784),B_24)) = k1_xboole_0
      | ~ r1_tarski(A_784,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_20,c_91915])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k10_relat_1(B_19,A_18),k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2065,plain,(
    ! [A_147,B_148,A_149] :
      ( r1_tarski(A_147,k1_relat_1(B_148))
      | ~ r1_tarski(A_147,k10_relat_1(B_148,A_149))
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_26,c_289])).

tff(c_2121,plain,(
    ! [B_150,A_151,B_152] :
      ( r1_tarski(k4_xboole_0(k10_relat_1(B_150,A_151),B_152),k1_relat_1(B_150))
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_16,c_2065])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k9_relat_1(B_17,A_16) != k1_xboole_0
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_210277,plain,(
    ! [B_1284,A_1285,B_1286] :
      ( k9_relat_1(B_1284,k4_xboole_0(k10_relat_1(B_1284,A_1285),B_1286)) != k1_xboole_0
      | k4_xboole_0(k10_relat_1(B_1284,A_1285),B_1286) = k1_xboole_0
      | ~ v1_relat_1(B_1284) ) ),
    inference(resolution,[status(thm)],[c_2121,c_24])).

tff(c_210375,plain,(
    ! [A_784,B_24] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_784),B_24) = k1_xboole_0
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_784,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92096,c_210277])).

tff(c_210551,plain,(
    ! [A_1287,B_1288] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_1287),B_1288) = k1_xboole_0
      | ~ r1_tarski(A_1287,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_210375])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_373,plain,(
    ! [A_65,B_66] :
      ( k2_xboole_0(A_65,B_66) = B_66
      | k4_xboole_0(A_65,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_349,c_12])).

tff(c_213401,plain,(
    ! [A_1296,B_1297] :
      ( k2_xboole_0(k10_relat_1('#skF_2',A_1296),B_1297) = B_1297
      | ~ r1_tarski(A_1296,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210551,c_373])).

tff(c_213562,plain,(
    ! [A_20,B_21] :
      ( k10_relat_1('#skF_2',k2_xboole_0(A_20,B_21)) = k10_relat_1('#skF_2',B_21)
      | ~ r1_tarski(A_20,k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_213401])).

tff(c_228307,plain,(
    ! [A_1338,B_1339] :
      ( k10_relat_1('#skF_2',k2_xboole_0(A_1338,B_1339)) = k10_relat_1('#skF_2',B_1339)
      | ~ r1_tarski(A_1338,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_213562])).

tff(c_228647,plain,(
    ! [B_1339,A_1338] :
      ( r1_tarski(k10_relat_1('#skF_2',B_1339),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_1338,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228307,c_26])).

tff(c_228961,plain,(
    ! [B_1339,A_1338] :
      ( r1_tarski(k10_relat_1('#skF_2',B_1339),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_1338,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_228647])).

tff(c_230713,plain,(
    ! [A_1343] : ~ r1_tarski(A_1343,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_228961])).

tff(c_230918,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_196181,c_230713])).

tff(c_230920,plain,(
    ! [B_1344] : r1_tarski(k10_relat_1('#skF_2',B_1344),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_228961])).

tff(c_232960,plain,(
    ! [A_1348,B_1349] :
      ( r1_tarski(A_1348,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_1348,k10_relat_1('#skF_2',B_1349)) ) ),
    inference(resolution,[status(thm)],[c_230920,c_14])).

tff(c_233533,plain,(
    ! [B_1349,B_11] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',B_1349),B_11),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_232960])).

tff(c_3399,plain,(
    ! [B_179,A_180] :
      ( k4_xboole_0(k9_relat_1(B_179,k10_relat_1(B_179,A_180)),A_180) = k1_xboole_0
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179) ) ),
    inference(resolution,[status(thm)],[c_325,c_10])).

tff(c_3446,plain,(
    ! [B_179,B_24] :
      ( k9_relat_1(B_179,k4_xboole_0(k10_relat_1(B_179,k9_relat_1(B_179,B_24)),B_24)) = k1_xboole_0
      | ~ v2_funct_1(B_179)
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179)
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_43])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k10_relat_1(B_29,k9_relat_1(B_29,A_28)))
      | ~ r1_tarski(A_28,k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1054,plain,(
    ! [A_28,B_112,B_29] :
      ( r1_tarski(A_28,B_112)
      | k4_xboole_0(k10_relat_1(B_29,k9_relat_1(B_29,A_28)),B_112) != k1_xboole_0
      | ~ r1_tarski(A_28,k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_1032])).

tff(c_210982,plain,(
    ! [A_28,B_1288] :
      ( r1_tarski(A_28,B_1288)
      | ~ r1_tarski(A_28,k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(k9_relat_1('#skF_2',A_28),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210551,c_1054])).

tff(c_311739,plain,(
    ! [A_1565,B_1566] :
      ( r1_tarski(A_1565,B_1566)
      | ~ r1_tarski(A_1565,k1_relat_1('#skF_2'))
      | ~ r1_tarski(k9_relat_1('#skF_2',A_1565),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_210982])).

tff(c_311832,plain,(
    ! [B_24,B_1566] :
      ( r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_24)),B_24),B_1566)
      | ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_24)),B_24),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3446,c_311739])).

tff(c_313629,plain,(
    ! [B_1569,B_1570] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1569)),B_1569),B_1570) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_42,c_40,c_38,c_94,c_233533,c_311832])).

tff(c_18,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_314185,plain,(
    ! [B_1569] : k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1569)),B_1569) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_313629,c_18])).

tff(c_146,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_158,plain,(
    k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_36])).

tff(c_314273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314185,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 59.61/49.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.72/49.20  
% 59.72/49.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.72/49.20  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 59.72/49.20  
% 59.72/49.20  %Foreground sorts:
% 59.72/49.20  
% 59.72/49.20  
% 59.72/49.20  %Background operators:
% 59.72/49.20  
% 59.72/49.20  
% 59.72/49.20  %Foreground operators:
% 59.72/49.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 59.72/49.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 59.72/49.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 59.72/49.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 59.72/49.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 59.72/49.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 59.72/49.20  tff('#skF_2', type, '#skF_2': $i).
% 59.72/49.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 59.72/49.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 59.72/49.20  tff('#skF_1', type, '#skF_1': $i).
% 59.72/49.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 59.72/49.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 59.72/49.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 59.72/49.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 59.72/49.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 59.72/49.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 59.72/49.20  
% 59.80/49.22  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 59.80/49.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 59.80/49.22  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 59.80/49.22  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 59.80/49.22  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 59.80/49.22  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 59.80/49.22  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 59.80/49.22  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 59.80/49.22  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 59.80/49.22  tff(f_53, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 59.80/49.22  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 59.80/49.22  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 59.80/49.22  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 59.80/49.22  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 59.80/49.22  tff(f_51, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 59.80/49.22  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.80/49.22  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.80/49.22  tff(c_38, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.80/49.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.80/49.22  tff(c_80, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 59.80/49.22  tff(c_89, plain, (![B_39]: (k4_xboole_0(B_39, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_80])).
% 59.80/49.22  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 59.80/49.22  tff(c_94, plain, (![B_39]: (r1_tarski(k1_xboole_0, B_39))), inference(superposition, [status(thm), theory('equality')], [c_89, c_16])).
% 59.80/49.22  tff(c_88, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_80])).
% 59.80/49.22  tff(c_22, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 59.80/49.22  tff(c_30, plain, (![C_25, A_23, B_24]: (k6_subset_1(k9_relat_1(C_25, A_23), k9_relat_1(C_25, B_24))=k9_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v2_funct_1(C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 59.80/49.22  tff(c_1252, plain, (![C_124, A_125, B_126]: (k4_xboole_0(k9_relat_1(C_124, A_125), k9_relat_1(C_124, B_126))=k9_relat_1(C_124, k4_xboole_0(A_125, B_126)) | ~v2_funct_1(C_124) | ~v1_funct_1(C_124) | ~v1_relat_1(C_124))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_30])).
% 59.80/49.22  tff(c_1300, plain, (![C_124, B_126]: (k9_relat_1(C_124, k4_xboole_0(B_126, B_126))=k1_xboole_0 | ~v2_funct_1(C_124) | ~v1_funct_1(C_124) | ~v1_relat_1(C_124))), inference(superposition, [status(thm), theory('equality')], [c_1252, c_88])).
% 59.80/49.22  tff(c_1322, plain, (![C_127]: (k9_relat_1(C_127, k1_xboole_0)=k1_xboole_0 | ~v2_funct_1(C_127) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1300])).
% 59.80/49.22  tff(c_1325, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_1322])).
% 59.80/49.22  tff(c_1328, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1325])).
% 59.80/49.22  tff(c_43, plain, (![C_25, A_23, B_24]: (k4_xboole_0(k9_relat_1(C_25, A_23), k9_relat_1(C_25, B_24))=k9_relat_1(C_25, k4_xboole_0(A_23, B_24)) | ~v2_funct_1(C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_30])).
% 59.80/49.22  tff(c_1335, plain, (![A_23]: (k9_relat_1('#skF_2', k4_xboole_0(A_23, k1_xboole_0))=k4_xboole_0(k9_relat_1('#skF_2', A_23), k1_xboole_0) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1328, c_43])).
% 59.80/49.22  tff(c_1344, plain, (![A_23]: (k9_relat_1('#skF_2', k4_xboole_0(A_23, k1_xboole_0))=k4_xboole_0(k9_relat_1('#skF_2', A_23), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_1335])).
% 59.80/49.22  tff(c_8843, plain, (![C_283, A_284, B_285]: (r1_tarski(k9_relat_1(C_283, k4_xboole_0(A_284, B_285)), k9_relat_1(C_283, A_284)) | ~v2_funct_1(C_283) | ~v1_funct_1(C_283) | ~v1_relat_1(C_283))), inference(superposition, [status(thm), theory('equality')], [c_1252, c_16])).
% 59.80/49.22  tff(c_8934, plain, (![A_23, B_285]: (r1_tarski(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(A_23, k1_xboole_0), B_285)), k4_xboole_0(k9_relat_1('#skF_2', A_23), k1_xboole_0)) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1344, c_8843])).
% 59.80/49.22  tff(c_42924, plain, (![A_561, B_562]: (r1_tarski(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(A_561, k1_xboole_0), B_562)), k4_xboole_0(k9_relat_1('#skF_2', A_561), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_8934])).
% 59.80/49.22  tff(c_289, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 59.80/49.22  tff(c_303, plain, (![A_58, A_10, B_11]: (r1_tarski(A_58, A_10) | ~r1_tarski(A_58, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_16, c_289])).
% 59.80/49.22  tff(c_43361, plain, (![A_561, B_562]: (r1_tarski(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(A_561, k1_xboole_0), B_562)), k9_relat_1('#skF_2', A_561)))), inference(resolution, [status(thm)], [c_42924, c_303])).
% 59.80/49.22  tff(c_50204, plain, (![A_593, C_594, A_595, B_596]: (r1_tarski(A_593, k9_relat_1(C_594, A_595)) | ~r1_tarski(A_593, k9_relat_1(C_594, k4_xboole_0(A_595, B_596))) | ~v2_funct_1(C_594) | ~v1_funct_1(C_594) | ~v1_relat_1(C_594))), inference(superposition, [status(thm), theory('equality')], [c_1252, c_303])).
% 59.80/49.22  tff(c_50224, plain, (![A_595, B_596, B_562]: (r1_tarski(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(k4_xboole_0(A_595, B_596), k1_xboole_0), B_562)), k9_relat_1('#skF_2', A_595)) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_43361, c_50204])).
% 59.80/49.22  tff(c_191389, plain, (![A_1222, B_1223, B_1224]: (r1_tarski(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(k4_xboole_0(A_1222, B_1223), k1_xboole_0), B_1224)), k9_relat_1('#skF_2', A_1222)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_50224])).
% 59.80/49.22  tff(c_325, plain, (![B_63, A_64]: (r1_tarski(k9_relat_1(B_63, k10_relat_1(B_63, A_64)), A_64) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_87])).
% 59.80/49.22  tff(c_14, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 59.80/49.22  tff(c_344, plain, (![A_7, A_64, B_63]: (r1_tarski(A_7, A_64) | ~r1_tarski(A_7, k9_relat_1(B_63, k10_relat_1(B_63, A_64))) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_325, c_14])).
% 59.80/49.22  tff(c_191414, plain, (![A_64, B_1223, B_1224]: (r1_tarski(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2', A_64), B_1223), k1_xboole_0), B_1224)), A_64) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_191389, c_344])).
% 59.80/49.22  tff(c_195609, plain, (![A_1233, B_1234, B_1235]: (r1_tarski(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2', A_1233), B_1234), k1_xboole_0), B_1235)), A_1233))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_191414])).
% 59.80/49.22  tff(c_196031, plain, (![A_1233, B_1234]: (r1_tarski(k4_xboole_0(k9_relat_1('#skF_2', k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2', A_1233), B_1234), k1_xboole_0)), k1_xboole_0), A_1233))), inference(superposition, [status(thm), theory('equality')], [c_1344, c_195609])).
% 59.80/49.22  tff(c_196181, plain, (![A_1233, B_1234]: (r1_tarski(k4_xboole_0(k4_xboole_0(k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', A_1233), B_1234)), k1_xboole_0), k1_xboole_0), A_1233))), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_196031])).
% 59.80/49.22  tff(c_28, plain, (![C_22, A_20, B_21]: (k2_xboole_0(k10_relat_1(C_22, A_20), k10_relat_1(C_22, B_21))=k10_relat_1(C_22, k2_xboole_0(A_20, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 59.80/49.22  tff(c_20, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 59.80/49.22  tff(c_26785, plain, (![C_446, A_447, B_448]: (r1_tarski(k9_relat_1(C_446, k4_xboole_0(k10_relat_1(C_446, A_447), B_448)), A_447) | ~v2_funct_1(C_446) | ~v1_funct_1(C_446) | ~v1_relat_1(C_446))), inference(resolution, [status(thm)], [c_8843, c_344])).
% 59.80/49.22  tff(c_26889, plain, (![A_447]: (r1_tarski(k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_447)), k1_xboole_0), A_447) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1344, c_26785])).
% 59.80/49.22  tff(c_26932, plain, (![A_449]: (r1_tarski(k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_449)), k1_xboole_0), A_449))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_26889])).
% 59.80/49.22  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 59.80/49.22  tff(c_27063, plain, (![A_449]: (k4_xboole_0(k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_449)), k1_xboole_0), A_449)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26932, c_10])).
% 59.80/49.22  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 59.80/49.22  tff(c_1032, plain, (![A_111, B_112, A_113]: (r1_tarski(A_111, B_112) | ~r1_tarski(A_111, A_113) | k4_xboole_0(A_113, B_112)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_289])).
% 59.80/49.22  tff(c_1064, plain, (![A_114, B_115, B_116]: (r1_tarski(k4_xboole_0(A_114, B_115), B_116) | k4_xboole_0(A_114, B_116)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1032])).
% 59.80/49.22  tff(c_1127, plain, (![A_114, B_115, B_116]: (k4_xboole_0(k4_xboole_0(A_114, B_115), B_116)=k1_xboole_0 | k4_xboole_0(A_114, B_116)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1064, c_10])).
% 59.80/49.22  tff(c_377, plain, (![A_67, A_68, B_69]: (r1_tarski(A_67, A_68) | ~r1_tarski(A_67, k4_xboole_0(A_68, B_69)))), inference(resolution, [status(thm)], [c_16, c_289])).
% 59.80/49.22  tff(c_419, plain, (![A_70, B_71, B_72]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_70, B_71), B_72), A_70))), inference(resolution, [status(thm)], [c_16, c_377])).
% 59.80/49.22  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.80/49.22  tff(c_36280, plain, (![A_502, B_503, B_504]: (k4_xboole_0(k4_xboole_0(A_502, B_503), B_504)=A_502 | ~r1_tarski(A_502, k4_xboole_0(k4_xboole_0(A_502, B_503), B_504)))), inference(resolution, [status(thm)], [c_419, c_2])).
% 59.80/49.22  tff(c_41062, plain, (![A_549, B_550, B_551]: (k4_xboole_0(k4_xboole_0(A_549, B_550), B_551)=A_549 | ~r1_tarski(A_549, k1_xboole_0) | k4_xboole_0(A_549, B_551)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1127, c_36280])).
% 59.80/49.22  tff(c_87, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_80])).
% 59.80/49.22  tff(c_47131, plain, (![A_577, B_578, B_579]: (k4_xboole_0(A_577, k4_xboole_0(A_577, B_578))=k1_xboole_0 | ~r1_tarski(A_577, k1_xboole_0) | k4_xboole_0(A_577, B_579)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_41062, c_87])).
% 59.80/49.22  tff(c_47285, plain, (![B_580, B_581]: (k4_xboole_0(B_580, k4_xboole_0(B_580, B_581))=k1_xboole_0 | ~r1_tarski(B_580, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88, c_47131])).
% 59.80/49.22  tff(c_1059, plain, (![A_3, B_112, B_4]: (r1_tarski(A_3, B_112) | k4_xboole_0(B_4, B_112)!=k1_xboole_0 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1032])).
% 59.80/49.22  tff(c_49756, plain, (![A_588, B_589, B_590]: (r1_tarski(A_588, k4_xboole_0(B_589, B_590)) | k4_xboole_0(A_588, B_589)!=k1_xboole_0 | ~r1_tarski(B_589, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_47285, c_1059])).
% 59.80/49.22  tff(c_50019, plain, (![A_591, B_592]: (r1_tarski(A_591, k1_xboole_0) | k4_xboole_0(A_591, B_592)!=k1_xboole_0 | ~r1_tarski(B_592, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88, c_49756])).
% 59.80/49.22  tff(c_90217, plain, (![A_779]: (r1_tarski(k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_779)), k1_xboole_0), k1_xboole_0) | ~r1_tarski(A_779, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_27063, c_50019])).
% 59.80/49.22  tff(c_305, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~r1_tarski(A_61, k1_xboole_0))), inference(resolution, [status(thm)], [c_94, c_289])).
% 59.80/49.22  tff(c_349, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | k4_xboole_0(A_65, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_305])).
% 59.80/49.22  tff(c_372, plain, (![B_66, A_65]: (B_66=A_65 | ~r1_tarski(B_66, A_65) | k4_xboole_0(A_65, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_349, c_2])).
% 59.80/49.22  tff(c_90239, plain, (![A_779]: (k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_779)), k1_xboole_0)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0 | ~r1_tarski(A_779, k1_xboole_0))), inference(resolution, [status(thm)], [c_90217, c_372])).
% 59.80/49.22  tff(c_90354, plain, (![A_780]: (k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_780)), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_780, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_90239])).
% 59.80/49.22  tff(c_318, plain, (![A_3, B_62]: (r1_tarski(A_3, B_62) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_305])).
% 59.80/49.22  tff(c_245, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.80/49.22  tff(c_765, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(B_91, A_92) | k4_xboole_0(A_92, B_91)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_245])).
% 59.80/49.22  tff(c_791, plain, (![B_62, A_3]: (B_62=A_3 | k4_xboole_0(B_62, A_3)!=k1_xboole_0 | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_318, c_765])).
% 59.80/49.22  tff(c_90757, plain, (![A_780]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_780))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0 | ~r1_tarski(A_780, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90354, c_791])).
% 59.80/49.22  tff(c_91577, plain, (![A_784]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_784))=k1_xboole_0 | ~r1_tarski(A_784, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_90757])).
% 59.80/49.22  tff(c_91915, plain, (![A_784, B_24]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', A_784), B_24))=k4_xboole_0(k1_xboole_0, k9_relat_1('#skF_2', B_24)) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_784, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_91577, c_43])).
% 59.80/49.22  tff(c_92096, plain, (![A_784, B_24]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', A_784), B_24))=k1_xboole_0 | ~r1_tarski(A_784, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_20, c_91915])).
% 59.80/49.22  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k10_relat_1(B_19, A_18), k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 59.80/49.22  tff(c_2065, plain, (![A_147, B_148, A_149]: (r1_tarski(A_147, k1_relat_1(B_148)) | ~r1_tarski(A_147, k10_relat_1(B_148, A_149)) | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_26, c_289])).
% 59.80/49.22  tff(c_2121, plain, (![B_150, A_151, B_152]: (r1_tarski(k4_xboole_0(k10_relat_1(B_150, A_151), B_152), k1_relat_1(B_150)) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_16, c_2065])).
% 59.80/49.22  tff(c_24, plain, (![B_17, A_16]: (k9_relat_1(B_17, A_16)!=k1_xboole_0 | ~r1_tarski(A_16, k1_relat_1(B_17)) | k1_xboole_0=A_16 | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 59.80/49.22  tff(c_210277, plain, (![B_1284, A_1285, B_1286]: (k9_relat_1(B_1284, k4_xboole_0(k10_relat_1(B_1284, A_1285), B_1286))!=k1_xboole_0 | k4_xboole_0(k10_relat_1(B_1284, A_1285), B_1286)=k1_xboole_0 | ~v1_relat_1(B_1284))), inference(resolution, [status(thm)], [c_2121, c_24])).
% 59.80/49.22  tff(c_210375, plain, (![A_784, B_24]: (k4_xboole_0(k10_relat_1('#skF_2', A_784), B_24)=k1_xboole_0 | ~v1_relat_1('#skF_2') | ~r1_tarski(A_784, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_92096, c_210277])).
% 59.80/49.22  tff(c_210551, plain, (![A_1287, B_1288]: (k4_xboole_0(k10_relat_1('#skF_2', A_1287), B_1288)=k1_xboole_0 | ~r1_tarski(A_1287, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_210375])).
% 59.80/49.22  tff(c_12, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 59.80/49.22  tff(c_373, plain, (![A_65, B_66]: (k2_xboole_0(A_65, B_66)=B_66 | k4_xboole_0(A_65, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_349, c_12])).
% 59.80/49.22  tff(c_213401, plain, (![A_1296, B_1297]: (k2_xboole_0(k10_relat_1('#skF_2', A_1296), B_1297)=B_1297 | ~r1_tarski(A_1296, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_210551, c_373])).
% 59.80/49.22  tff(c_213562, plain, (![A_20, B_21]: (k10_relat_1('#skF_2', k2_xboole_0(A_20, B_21))=k10_relat_1('#skF_2', B_21) | ~r1_tarski(A_20, k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_213401])).
% 59.80/49.22  tff(c_228307, plain, (![A_1338, B_1339]: (k10_relat_1('#skF_2', k2_xboole_0(A_1338, B_1339))=k10_relat_1('#skF_2', B_1339) | ~r1_tarski(A_1338, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_213562])).
% 59.80/49.22  tff(c_228647, plain, (![B_1339, A_1338]: (r1_tarski(k10_relat_1('#skF_2', B_1339), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~r1_tarski(A_1338, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_228307, c_26])).
% 59.80/49.22  tff(c_228961, plain, (![B_1339, A_1338]: (r1_tarski(k10_relat_1('#skF_2', B_1339), k1_relat_1('#skF_2')) | ~r1_tarski(A_1338, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_228647])).
% 59.80/49.22  tff(c_230713, plain, (![A_1343]: (~r1_tarski(A_1343, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_228961])).
% 59.80/49.22  tff(c_230918, plain, $false, inference(resolution, [status(thm)], [c_196181, c_230713])).
% 59.80/49.22  tff(c_230920, plain, (![B_1344]: (r1_tarski(k10_relat_1('#skF_2', B_1344), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_228961])).
% 59.80/49.22  tff(c_232960, plain, (![A_1348, B_1349]: (r1_tarski(A_1348, k1_relat_1('#skF_2')) | ~r1_tarski(A_1348, k10_relat_1('#skF_2', B_1349)))), inference(resolution, [status(thm)], [c_230920, c_14])).
% 59.80/49.22  tff(c_233533, plain, (![B_1349, B_11]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', B_1349), B_11), k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_232960])).
% 59.80/49.22  tff(c_3399, plain, (![B_179, A_180]: (k4_xboole_0(k9_relat_1(B_179, k10_relat_1(B_179, A_180)), A_180)=k1_xboole_0 | ~v1_funct_1(B_179) | ~v1_relat_1(B_179))), inference(resolution, [status(thm)], [c_325, c_10])).
% 59.80/49.22  tff(c_3446, plain, (![B_179, B_24]: (k9_relat_1(B_179, k4_xboole_0(k10_relat_1(B_179, k9_relat_1(B_179, B_24)), B_24))=k1_xboole_0 | ~v2_funct_1(B_179) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179))), inference(superposition, [status(thm), theory('equality')], [c_3399, c_43])).
% 59.80/49.22  tff(c_34, plain, (![A_28, B_29]: (r1_tarski(A_28, k10_relat_1(B_29, k9_relat_1(B_29, A_28))) | ~r1_tarski(A_28, k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 59.80/49.22  tff(c_1054, plain, (![A_28, B_112, B_29]: (r1_tarski(A_28, B_112) | k4_xboole_0(k10_relat_1(B_29, k9_relat_1(B_29, A_28)), B_112)!=k1_xboole_0 | ~r1_tarski(A_28, k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_34, c_1032])).
% 59.80/49.22  tff(c_210982, plain, (![A_28, B_1288]: (r1_tarski(A_28, B_1288) | ~r1_tarski(A_28, k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~r1_tarski(k9_relat_1('#skF_2', A_28), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_210551, c_1054])).
% 59.80/49.22  tff(c_311739, plain, (![A_1565, B_1566]: (r1_tarski(A_1565, B_1566) | ~r1_tarski(A_1565, k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', A_1565), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_210982])).
% 59.80/49.22  tff(c_311832, plain, (![B_24, B_1566]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_24)), B_24), B_1566) | ~r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_24)), B_24), k1_relat_1('#skF_2')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3446, c_311739])).
% 59.80/49.22  tff(c_313629, plain, (![B_1569, B_1570]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1569)), B_1569), B_1570))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_42, c_40, c_38, c_94, c_233533, c_311832])).
% 59.80/49.22  tff(c_18, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 59.80/49.22  tff(c_314185, plain, (![B_1569]: (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1569)), B_1569)=k1_xboole_0)), inference(resolution, [status(thm)], [c_313629, c_18])).
% 59.80/49.22  tff(c_146, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 59.80/49.22  tff(c_36, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.80/49.22  tff(c_158, plain, (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_36])).
% 59.80/49.22  tff(c_314273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314185, c_158])).
% 59.80/49.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.80/49.22  
% 59.80/49.22  Inference rules
% 59.80/49.22  ----------------------
% 59.80/49.22  #Ref     : 0
% 59.80/49.22  #Sup     : 76618
% 59.80/49.22  #Fact    : 0
% 59.80/49.22  #Define  : 0
% 59.80/49.22  #Split   : 4
% 59.80/49.22  #Chain   : 0
% 59.80/49.22  #Close   : 0
% 59.80/49.22  
% 59.80/49.22  Ordering : KBO
% 59.80/49.22  
% 59.80/49.22  Simplification rules
% 59.80/49.22  ----------------------
% 59.80/49.22  #Subsume      : 24025
% 59.80/49.22  #Demod        : 106611
% 59.80/49.22  #Tautology    : 36166
% 59.80/49.22  #SimpNegUnit  : 61
% 59.80/49.22  #BackRed      : 2
% 59.80/49.22  
% 59.80/49.22  #Partial instantiations: 0
% 59.80/49.22  #Strategies tried      : 1
% 59.80/49.22  
% 59.80/49.22  Timing (in seconds)
% 59.80/49.22  ----------------------
% 59.80/49.23  Preprocessing        : 0.29
% 59.80/49.23  Parsing              : 0.15
% 59.80/49.23  CNF conversion       : 0.02
% 59.80/49.23  Main loop            : 48.10
% 59.80/49.23  Inferencing          : 4.64
% 59.80/49.23  Reduction            : 18.58
% 59.80/49.23  Demodulation         : 15.82
% 59.80/49.23  BG Simplification    : 0.53
% 59.80/49.23  Subsumption          : 22.71
% 59.80/49.23  Abstraction          : 1.02
% 59.80/49.23  MUC search           : 0.00
% 59.80/49.23  Cooper               : 0.00
% 59.80/49.23  Total                : 48.44
% 59.80/49.23  Index Insertion      : 0.00
% 59.80/49.23  Index Deletion       : 0.00
% 59.80/49.23  Index Matching       : 0.00
% 59.80/49.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
