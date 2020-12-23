%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:59 EST 2020

% Result     : Theorem 4.98s
% Output     : CNFRefutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 260 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 582 expanded)
%              Number of equality atoms :    5 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k7_relat_1(B_28,A_27),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_114,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k2_relat_1(A_55),k2_relat_1(B_56))
      | ~ r1_tarski(A_55,B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1345,plain,(
    ! [B_193,A_194,B_195] :
      ( r1_tarski(k9_relat_1(B_193,A_194),k2_relat_1(B_195))
      | ~ r1_tarski(k7_relat_1(B_193,A_194),B_195)
      | ~ v1_relat_1(B_195)
      | ~ v1_relat_1(k7_relat_1(B_193,A_194))
      | ~ v1_relat_1(B_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(A_8)
      | ~ v1_relat_1(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_57])).

tff(c_1453,plain,(
    ! [B_206,A_207,B_208] :
      ( v1_relat_1(k9_relat_1(B_206,A_207))
      | ~ v1_relat_1(k2_relat_1(B_208))
      | ~ r1_tarski(k7_relat_1(B_206,A_207),B_208)
      | ~ v1_relat_1(B_208)
      | ~ v1_relat_1(k7_relat_1(B_206,A_207))
      | ~ v1_relat_1(B_206) ) ),
    inference(resolution,[status(thm)],[c_1345,c_61])).

tff(c_1504,plain,(
    ! [B_213,A_214] :
      ( v1_relat_1(k9_relat_1(B_213,A_214))
      | ~ v1_relat_1(k2_relat_1(B_213))
      | ~ v1_relat_1(k7_relat_1(B_213,A_214))
      | ~ v1_relat_1(B_213) ) ),
    inference(resolution,[status(thm)],[c_26,c_1453])).

tff(c_85,plain,(
    ! [C_50,A_51,B_52] :
      ( k7_relat_1(k7_relat_1(C_50,A_51),B_52) = k7_relat_1(C_50,k3_xboole_0(A_51,B_52))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [C_50,A_51,B_52] :
      ( r1_tarski(k7_relat_1(C_50,k3_xboole_0(A_51,B_52)),k7_relat_1(C_50,A_51))
      | ~ v1_relat_1(k7_relat_1(C_50,A_51))
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_26])).

tff(c_200,plain,(
    ! [A_79,B_80,A_81] :
      ( r1_tarski(k2_relat_1(A_79),k9_relat_1(B_80,A_81))
      | ~ r1_tarski(A_79,k7_relat_1(B_80,A_81))
      | ~ v1_relat_1(k7_relat_1(B_80,A_81))
      | ~ v1_relat_1(A_79)
      | ~ v1_relat_1(B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_1206,plain,(
    ! [B_177,A_178,B_179,A_180] :
      ( r1_tarski(k9_relat_1(B_177,A_178),k9_relat_1(B_179,A_180))
      | ~ r1_tarski(k7_relat_1(B_177,A_178),k7_relat_1(B_179,A_180))
      | ~ v1_relat_1(k7_relat_1(B_179,A_180))
      | ~ v1_relat_1(k7_relat_1(B_177,A_178))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(B_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_200])).

tff(c_76,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(A_47,k3_xboole_0(B_48,C_49))
      | ~ r1_tarski(A_47,C_49)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_83,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_28])).

tff(c_141,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_1213,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1206,c_141])).

tff(c_1245,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1213])).

tff(c_1247,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1245])).

tff(c_1250,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1247])).

tff(c_1254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1250])).

tff(c_1255,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1245])).

tff(c_1257,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1255])).

tff(c_1260,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_1257])).

tff(c_1263,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1260])).

tff(c_1266,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1263])).

tff(c_1270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1266])).

tff(c_1271,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1255])).

tff(c_1275,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1271])).

tff(c_1279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1275])).

tff(c_1281,plain,(
    r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1285,plain,
    ( v1_relat_1(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1281,c_61])).

tff(c_1286,plain,(
    ~ v1_relat_1(k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1285])).

tff(c_1507,plain,
    ( ~ v1_relat_1(k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1504,c_1286])).

tff(c_1513,plain,
    ( ~ v1_relat_1(k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1507])).

tff(c_1514,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1513])).

tff(c_1517,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1514])).

tff(c_1521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1517])).

tff(c_1523,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1513])).

tff(c_16,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_17,A_15),B_16) = k7_relat_1(C_17,k3_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_125,plain,(
    ! [B_57,A_58,C_59] :
      ( r1_tarski(k7_relat_1(B_57,A_58),k7_relat_1(C_59,A_58))
      | ~ r1_tarski(B_57,C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_131,plain,(
    ! [C_17,A_15,B_16,C_59] :
      ( r1_tarski(k7_relat_1(C_17,k3_xboole_0(A_15,B_16)),k7_relat_1(C_59,B_16))
      | ~ r1_tarski(k7_relat_1(C_17,A_15),C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(k7_relat_1(C_17,A_15))
      | ~ v1_relat_1(C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_125])).

tff(c_1359,plain,(
    ! [A_196,B_197,A_198] :
      ( r1_tarski(k2_relat_1(A_196),k9_relat_1(B_197,A_198))
      | ~ r1_tarski(A_196,k7_relat_1(B_197,A_198))
      | ~ v1_relat_1(k7_relat_1(B_197,A_198))
      | ~ v1_relat_1(A_196)
      | ~ v1_relat_1(B_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_2274,plain,(
    ! [B_282,A_283,B_284,A_285] :
      ( r1_tarski(k9_relat_1(B_282,A_283),k9_relat_1(B_284,A_285))
      | ~ r1_tarski(k7_relat_1(B_282,A_283),k7_relat_1(B_284,A_285))
      | ~ v1_relat_1(k7_relat_1(B_284,A_285))
      | ~ v1_relat_1(k7_relat_1(B_282,A_283))
      | ~ v1_relat_1(B_284)
      | ~ v1_relat_1(B_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1359])).

tff(c_1280,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2279,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2274,c_1280])).

tff(c_2310,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2279])).

tff(c_2312,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2310])).

tff(c_2315,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2312])).

tff(c_2319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2315])).

tff(c_2320,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2310])).

tff(c_2322,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2320])).

tff(c_2325,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_2322])).

tff(c_2328,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1523,c_2325])).

tff(c_2331,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_2328])).

tff(c_2335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2331])).

tff(c_2336,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2320])).

tff(c_2340,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2336])).

tff(c_2344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:14:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.98/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.98/1.85  
% 4.98/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.98/1.85  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.98/1.85  
% 4.98/1.85  %Foreground sorts:
% 4.98/1.85  
% 4.98/1.85  
% 4.98/1.85  %Background operators:
% 4.98/1.85  
% 4.98/1.85  
% 4.98/1.85  %Foreground operators:
% 4.98/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.98/1.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.98/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.98/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.98/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.98/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.98/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.98/1.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.98/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.98/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.98/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.98/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.98/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.98/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.98/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.98/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.98/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.98/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.98/1.85  
% 4.98/1.87  tff(f_87, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 4.98/1.87  tff(f_50, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.98/1.87  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.98/1.87  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.98/1.87  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.98/1.87  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.98/1.87  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.98/1.87  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 4.98/1.87  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.98/1.87  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 4.98/1.87  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.98/1.87  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.98/1.87  tff(c_26, plain, (![B_28, A_27]: (r1_tarski(k7_relat_1(B_28, A_27), B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.98/1.87  tff(c_20, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.98/1.87  tff(c_114, plain, (![A_55, B_56]: (r1_tarski(k2_relat_1(A_55), k2_relat_1(B_56)) | ~r1_tarski(A_55, B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.98/1.87  tff(c_1345, plain, (![B_193, A_194, B_195]: (r1_tarski(k9_relat_1(B_193, A_194), k2_relat_1(B_195)) | ~r1_tarski(k7_relat_1(B_193, A_194), B_195) | ~v1_relat_1(B_195) | ~v1_relat_1(k7_relat_1(B_193, A_194)) | ~v1_relat_1(B_193))), inference(superposition, [status(thm), theory('equality')], [c_20, c_114])).
% 4.98/1.87  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.98/1.87  tff(c_57, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.98/1.87  tff(c_61, plain, (![A_8, B_9]: (v1_relat_1(A_8) | ~v1_relat_1(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_10, c_57])).
% 4.98/1.87  tff(c_1453, plain, (![B_206, A_207, B_208]: (v1_relat_1(k9_relat_1(B_206, A_207)) | ~v1_relat_1(k2_relat_1(B_208)) | ~r1_tarski(k7_relat_1(B_206, A_207), B_208) | ~v1_relat_1(B_208) | ~v1_relat_1(k7_relat_1(B_206, A_207)) | ~v1_relat_1(B_206))), inference(resolution, [status(thm)], [c_1345, c_61])).
% 4.98/1.87  tff(c_1504, plain, (![B_213, A_214]: (v1_relat_1(k9_relat_1(B_213, A_214)) | ~v1_relat_1(k2_relat_1(B_213)) | ~v1_relat_1(k7_relat_1(B_213, A_214)) | ~v1_relat_1(B_213))), inference(resolution, [status(thm)], [c_26, c_1453])).
% 4.98/1.87  tff(c_85, plain, (![C_50, A_51, B_52]: (k7_relat_1(k7_relat_1(C_50, A_51), B_52)=k7_relat_1(C_50, k3_xboole_0(A_51, B_52)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.98/1.87  tff(c_97, plain, (![C_50, A_51, B_52]: (r1_tarski(k7_relat_1(C_50, k3_xboole_0(A_51, B_52)), k7_relat_1(C_50, A_51)) | ~v1_relat_1(k7_relat_1(C_50, A_51)) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_85, c_26])).
% 4.98/1.87  tff(c_200, plain, (![A_79, B_80, A_81]: (r1_tarski(k2_relat_1(A_79), k9_relat_1(B_80, A_81)) | ~r1_tarski(A_79, k7_relat_1(B_80, A_81)) | ~v1_relat_1(k7_relat_1(B_80, A_81)) | ~v1_relat_1(A_79) | ~v1_relat_1(B_80))), inference(superposition, [status(thm), theory('equality')], [c_20, c_114])).
% 4.98/1.87  tff(c_1206, plain, (![B_177, A_178, B_179, A_180]: (r1_tarski(k9_relat_1(B_177, A_178), k9_relat_1(B_179, A_180)) | ~r1_tarski(k7_relat_1(B_177, A_178), k7_relat_1(B_179, A_180)) | ~v1_relat_1(k7_relat_1(B_179, A_180)) | ~v1_relat_1(k7_relat_1(B_177, A_178)) | ~v1_relat_1(B_179) | ~v1_relat_1(B_177))), inference(superposition, [status(thm), theory('equality')], [c_20, c_200])).
% 4.98/1.87  tff(c_76, plain, (![A_47, B_48, C_49]: (r1_tarski(A_47, k3_xboole_0(B_48, C_49)) | ~r1_tarski(A_47, C_49) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.98/1.87  tff(c_28, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.98/1.87  tff(c_83, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_28])).
% 4.98/1.87  tff(c_141, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_83])).
% 4.98/1.87  tff(c_1213, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1206, c_141])).
% 4.98/1.87  tff(c_1245, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1213])).
% 4.98/1.87  tff(c_1247, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1245])).
% 4.98/1.87  tff(c_1250, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1247])).
% 4.98/1.87  tff(c_1254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1250])).
% 4.98/1.87  tff(c_1255, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_1245])).
% 4.98/1.87  tff(c_1257, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1255])).
% 4.98/1.87  tff(c_1260, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_97, c_1257])).
% 4.98/1.87  tff(c_1263, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1260])).
% 4.98/1.87  tff(c_1266, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1263])).
% 4.98/1.87  tff(c_1270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1266])).
% 4.98/1.87  tff(c_1271, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_1255])).
% 4.98/1.87  tff(c_1275, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1271])).
% 4.98/1.87  tff(c_1279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1275])).
% 4.98/1.87  tff(c_1281, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_83])).
% 4.98/1.87  tff(c_1285, plain, (v1_relat_1(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_1281, c_61])).
% 4.98/1.87  tff(c_1286, plain, (~v1_relat_1(k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1285])).
% 4.98/1.87  tff(c_1507, plain, (~v1_relat_1(k2_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1504, c_1286])).
% 4.98/1.87  tff(c_1513, plain, (~v1_relat_1(k2_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1507])).
% 4.98/1.87  tff(c_1514, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1513])).
% 4.98/1.87  tff(c_1517, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1514])).
% 4.98/1.87  tff(c_1521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1517])).
% 4.98/1.87  tff(c_1523, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_1513])).
% 4.98/1.87  tff(c_16, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k7_relat_1(C_17, k3_xboole_0(A_15, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.98/1.87  tff(c_125, plain, (![B_57, A_58, C_59]: (r1_tarski(k7_relat_1(B_57, A_58), k7_relat_1(C_59, A_58)) | ~r1_tarski(B_57, C_59) | ~v1_relat_1(C_59) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.98/1.87  tff(c_131, plain, (![C_17, A_15, B_16, C_59]: (r1_tarski(k7_relat_1(C_17, k3_xboole_0(A_15, B_16)), k7_relat_1(C_59, B_16)) | ~r1_tarski(k7_relat_1(C_17, A_15), C_59) | ~v1_relat_1(C_59) | ~v1_relat_1(k7_relat_1(C_17, A_15)) | ~v1_relat_1(C_17))), inference(superposition, [status(thm), theory('equality')], [c_16, c_125])).
% 4.98/1.87  tff(c_1359, plain, (![A_196, B_197, A_198]: (r1_tarski(k2_relat_1(A_196), k9_relat_1(B_197, A_198)) | ~r1_tarski(A_196, k7_relat_1(B_197, A_198)) | ~v1_relat_1(k7_relat_1(B_197, A_198)) | ~v1_relat_1(A_196) | ~v1_relat_1(B_197))), inference(superposition, [status(thm), theory('equality')], [c_20, c_114])).
% 4.98/1.87  tff(c_2274, plain, (![B_282, A_283, B_284, A_285]: (r1_tarski(k9_relat_1(B_282, A_283), k9_relat_1(B_284, A_285)) | ~r1_tarski(k7_relat_1(B_282, A_283), k7_relat_1(B_284, A_285)) | ~v1_relat_1(k7_relat_1(B_284, A_285)) | ~v1_relat_1(k7_relat_1(B_282, A_283)) | ~v1_relat_1(B_284) | ~v1_relat_1(B_282))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1359])).
% 4.98/1.87  tff(c_1280, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_83])).
% 4.98/1.87  tff(c_2279, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2274, c_1280])).
% 4.98/1.87  tff(c_2310, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2279])).
% 4.98/1.87  tff(c_2312, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2310])).
% 4.98/1.87  tff(c_2315, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_2312])).
% 4.98/1.87  tff(c_2319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2315])).
% 4.98/1.87  tff(c_2320, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2310])).
% 4.98/1.87  tff(c_2322, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2320])).
% 4.98/1.87  tff(c_2325, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_2322])).
% 4.98/1.87  tff(c_2328, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1523, c_2325])).
% 4.98/1.87  tff(c_2331, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_2328])).
% 4.98/1.87  tff(c_2335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2331])).
% 4.98/1.87  tff(c_2336, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2320])).
% 4.98/1.87  tff(c_2340, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_2336])).
% 4.98/1.87  tff(c_2344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2340])).
% 4.98/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.98/1.87  
% 4.98/1.87  Inference rules
% 4.98/1.87  ----------------------
% 4.98/1.87  #Ref     : 0
% 4.98/1.87  #Sup     : 651
% 4.98/1.87  #Fact    : 0
% 4.98/1.87  #Define  : 0
% 4.98/1.87  #Split   : 7
% 4.98/1.87  #Chain   : 0
% 4.98/1.87  #Close   : 0
% 4.98/1.87  
% 4.98/1.87  Ordering : KBO
% 4.98/1.87  
% 4.98/1.87  Simplification rules
% 4.98/1.87  ----------------------
% 4.98/1.87  #Subsume      : 47
% 4.98/1.87  #Demod        : 13
% 4.98/1.87  #Tautology    : 41
% 4.98/1.87  #SimpNegUnit  : 0
% 4.98/1.87  #BackRed      : 0
% 4.98/1.87  
% 4.98/1.87  #Partial instantiations: 0
% 4.98/1.87  #Strategies tried      : 1
% 4.98/1.87  
% 4.98/1.87  Timing (in seconds)
% 4.98/1.87  ----------------------
% 4.98/1.87  Preprocessing        : 0.30
% 4.98/1.87  Parsing              : 0.16
% 4.98/1.87  CNF conversion       : 0.02
% 4.98/1.87  Main loop            : 0.79
% 4.98/1.87  Inferencing          : 0.33
% 4.98/1.87  Reduction            : 0.17
% 4.98/1.87  Demodulation         : 0.12
% 4.98/1.87  BG Simplification    : 0.05
% 4.98/1.88  Subsumption          : 0.20
% 4.98/1.88  Abstraction          : 0.04
% 4.98/1.88  MUC search           : 0.00
% 4.98/1.88  Cooper               : 0.00
% 4.98/1.88  Total                : 1.13
% 4.98/1.88  Index Insertion      : 0.00
% 4.98/1.88  Index Deletion       : 0.00
% 4.98/1.88  Index Matching       : 0.00
% 4.98/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
