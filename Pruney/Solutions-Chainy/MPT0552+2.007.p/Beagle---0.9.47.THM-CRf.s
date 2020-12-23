%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:57 EST 2020

% Result     : Theorem 4.99s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 187 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 386 expanded)
%              Number of equality atoms :   11 (  36 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_10])).

tff(c_237,plain,(
    ! [C_64,A_65,B_66] :
      ( k3_xboole_0(k7_relat_1(C_64,A_65),k7_relat_1(C_64,B_66)) = k7_relat_1(C_64,k3_xboole_0(A_65,B_66))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_273,plain,(
    ! [C_67,A_68,B_69] :
      ( r1_tarski(k7_relat_1(C_67,k3_xboole_0(A_68,B_69)),k7_relat_1(C_67,A_68))
      | ~ v1_relat_1(C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_2])).

tff(c_282,plain,(
    ! [C_67,B_41,A_42] :
      ( r1_tarski(k7_relat_1(C_67,k3_xboole_0(B_41,A_42)),k7_relat_1(C_67,A_42))
      | ~ v1_relat_1(C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_273])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_221,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k2_relat_1(A_60),k2_relat_1(B_61))
      | ~ r1_tarski(A_60,B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1479,plain,(
    ! [B_172,A_173,B_174] :
      ( r1_tarski(k9_relat_1(B_172,A_173),k2_relat_1(B_174))
      | ~ r1_tarski(k7_relat_1(B_172,A_173),B_174)
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(k7_relat_1(B_172,A_173))
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_221])).

tff(c_2130,plain,(
    ! [B_227,A_228,B_229,A_230] :
      ( r1_tarski(k9_relat_1(B_227,A_228),k9_relat_1(B_229,A_230))
      | ~ r1_tarski(k7_relat_1(B_227,A_228),k7_relat_1(B_229,A_230))
      | ~ v1_relat_1(k7_relat_1(B_229,A_230))
      | ~ v1_relat_1(k7_relat_1(B_227,A_228))
      | ~ v1_relat_1(B_227)
      | ~ v1_relat_1(B_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1479])).

tff(c_261,plain,(
    ! [C_64,A_65,B_66] :
      ( r1_tarski(k7_relat_1(C_64,k3_xboole_0(A_65,B_66)),k7_relat_1(C_64,A_65))
      | ~ v1_relat_1(C_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_2])).

tff(c_319,plain,(
    ! [A_80,B_81,A_82] :
      ( r1_tarski(k2_relat_1(A_80),k9_relat_1(B_81,A_82))
      | ~ r1_tarski(A_80,k7_relat_1(B_81,A_82))
      | ~ v1_relat_1(k7_relat_1(B_81,A_82))
      | ~ v1_relat_1(A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_221])).

tff(c_1338,plain,(
    ! [B_154,A_155,B_156,A_157] :
      ( r1_tarski(k9_relat_1(B_154,A_155),k9_relat_1(B_156,A_157))
      | ~ r1_tarski(k7_relat_1(B_154,A_155),k7_relat_1(B_156,A_157))
      | ~ v1_relat_1(k7_relat_1(B_156,A_157))
      | ~ v1_relat_1(k7_relat_1(B_154,A_155))
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_319])).

tff(c_206,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k3_xboole_0(B_58,C_59))
      | ~ r1_tarski(A_57,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_220,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_206,c_28])).

tff(c_301,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_1341,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1338,c_301])).

tff(c_1359,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1341])).

tff(c_1361,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1359])).

tff(c_1364,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1361])).

tff(c_1368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1364])).

tff(c_1369,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1359])).

tff(c_1371,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1369])).

tff(c_1374,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_261,c_1371])).

tff(c_1378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1374])).

tff(c_1379,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_1383,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1379])).

tff(c_1387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1383])).

tff(c_1388,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_2133,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2130,c_1388])).

tff(c_2151,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2133])).

tff(c_2187,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2151])).

tff(c_2190,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2187])).

tff(c_2194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2190])).

tff(c_2195,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2151])).

tff(c_2197,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2195])).

tff(c_2200,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_282,c_2197])).

tff(c_2204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2200])).

tff(c_2205,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2195])).

tff(c_2209,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2205])).

tff(c_2213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.99/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.93  
% 4.99/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.93  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.99/1.93  
% 4.99/1.93  %Foreground sorts:
% 4.99/1.93  
% 4.99/1.93  
% 4.99/1.93  %Background operators:
% 4.99/1.93  
% 4.99/1.93  
% 4.99/1.93  %Foreground operators:
% 4.99/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/1.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.99/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.99/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.99/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.99/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.99/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.99/1.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.99/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.99/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.99/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.99/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.99/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.99/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.99/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.99/1.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.99/1.93  
% 4.99/1.95  tff(f_78, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 4.99/1.95  tff(f_54, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.99/1.95  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.99/1.95  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.99/1.95  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 4.99/1.95  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.99/1.95  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.99/1.95  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.99/1.95  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.99/1.95  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.99/1.95  tff(c_18, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.99/1.95  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.99/1.95  tff(c_81, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.99/1.95  tff(c_96, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_81])).
% 4.99/1.95  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.99/1.95  tff(c_102, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_96, c_10])).
% 4.99/1.95  tff(c_237, plain, (![C_64, A_65, B_66]: (k3_xboole_0(k7_relat_1(C_64, A_65), k7_relat_1(C_64, B_66))=k7_relat_1(C_64, k3_xboole_0(A_65, B_66)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.99/1.95  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.99/1.95  tff(c_273, plain, (![C_67, A_68, B_69]: (r1_tarski(k7_relat_1(C_67, k3_xboole_0(A_68, B_69)), k7_relat_1(C_67, A_68)) | ~v1_relat_1(C_67))), inference(superposition, [status(thm), theory('equality')], [c_237, c_2])).
% 4.99/1.95  tff(c_282, plain, (![C_67, B_41, A_42]: (r1_tarski(k7_relat_1(C_67, k3_xboole_0(B_41, A_42)), k7_relat_1(C_67, A_42)) | ~v1_relat_1(C_67))), inference(superposition, [status(thm), theory('equality')], [c_102, c_273])).
% 4.99/1.95  tff(c_22, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.99/1.95  tff(c_221, plain, (![A_60, B_61]: (r1_tarski(k2_relat_1(A_60), k2_relat_1(B_61)) | ~r1_tarski(A_60, B_61) | ~v1_relat_1(B_61) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.99/1.95  tff(c_1479, plain, (![B_172, A_173, B_174]: (r1_tarski(k9_relat_1(B_172, A_173), k2_relat_1(B_174)) | ~r1_tarski(k7_relat_1(B_172, A_173), B_174) | ~v1_relat_1(B_174) | ~v1_relat_1(k7_relat_1(B_172, A_173)) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_22, c_221])).
% 4.99/1.95  tff(c_2130, plain, (![B_227, A_228, B_229, A_230]: (r1_tarski(k9_relat_1(B_227, A_228), k9_relat_1(B_229, A_230)) | ~r1_tarski(k7_relat_1(B_227, A_228), k7_relat_1(B_229, A_230)) | ~v1_relat_1(k7_relat_1(B_229, A_230)) | ~v1_relat_1(k7_relat_1(B_227, A_228)) | ~v1_relat_1(B_227) | ~v1_relat_1(B_229))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1479])).
% 4.99/1.95  tff(c_261, plain, (![C_64, A_65, B_66]: (r1_tarski(k7_relat_1(C_64, k3_xboole_0(A_65, B_66)), k7_relat_1(C_64, A_65)) | ~v1_relat_1(C_64))), inference(superposition, [status(thm), theory('equality')], [c_237, c_2])).
% 4.99/1.95  tff(c_319, plain, (![A_80, B_81, A_82]: (r1_tarski(k2_relat_1(A_80), k9_relat_1(B_81, A_82)) | ~r1_tarski(A_80, k7_relat_1(B_81, A_82)) | ~v1_relat_1(k7_relat_1(B_81, A_82)) | ~v1_relat_1(A_80) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_22, c_221])).
% 4.99/1.95  tff(c_1338, plain, (![B_154, A_155, B_156, A_157]: (r1_tarski(k9_relat_1(B_154, A_155), k9_relat_1(B_156, A_157)) | ~r1_tarski(k7_relat_1(B_154, A_155), k7_relat_1(B_156, A_157)) | ~v1_relat_1(k7_relat_1(B_156, A_157)) | ~v1_relat_1(k7_relat_1(B_154, A_155)) | ~v1_relat_1(B_156) | ~v1_relat_1(B_154))), inference(superposition, [status(thm), theory('equality')], [c_22, c_319])).
% 4.99/1.95  tff(c_206, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k3_xboole_0(B_58, C_59)) | ~r1_tarski(A_57, C_59) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.99/1.95  tff(c_28, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.99/1.95  tff(c_220, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_206, c_28])).
% 4.99/1.95  tff(c_301, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_220])).
% 4.99/1.95  tff(c_1341, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1338, c_301])).
% 4.99/1.95  tff(c_1359, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1341])).
% 4.99/1.95  tff(c_1361, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1359])).
% 4.99/1.95  tff(c_1364, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1361])).
% 4.99/1.95  tff(c_1368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1364])).
% 4.99/1.95  tff(c_1369, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_1359])).
% 4.99/1.95  tff(c_1371, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1369])).
% 4.99/1.95  tff(c_1374, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_261, c_1371])).
% 4.99/1.95  tff(c_1378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1374])).
% 4.99/1.95  tff(c_1379, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_1369])).
% 4.99/1.95  tff(c_1383, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1379])).
% 4.99/1.95  tff(c_1387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1383])).
% 4.99/1.95  tff(c_1388, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_220])).
% 4.99/1.95  tff(c_2133, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2130, c_1388])).
% 4.99/1.95  tff(c_2151, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2133])).
% 4.99/1.95  tff(c_2187, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2151])).
% 4.99/1.95  tff(c_2190, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2187])).
% 4.99/1.95  tff(c_2194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2190])).
% 4.99/1.95  tff(c_2195, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2151])).
% 4.99/1.95  tff(c_2197, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2195])).
% 4.99/1.95  tff(c_2200, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_282, c_2197])).
% 4.99/1.95  tff(c_2204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2200])).
% 4.99/1.95  tff(c_2205, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2195])).
% 4.99/1.95  tff(c_2209, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2205])).
% 4.99/1.95  tff(c_2213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2209])).
% 4.99/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.95  
% 4.99/1.95  Inference rules
% 4.99/1.95  ----------------------
% 4.99/1.95  #Ref     : 0
% 4.99/1.95  #Sup     : 628
% 4.99/1.95  #Fact    : 0
% 4.99/1.95  #Define  : 0
% 4.99/1.95  #Split   : 6
% 4.99/1.95  #Chain   : 0
% 4.99/1.95  #Close   : 0
% 4.99/1.95  
% 4.99/1.95  Ordering : KBO
% 4.99/1.95  
% 4.99/1.95  Simplification rules
% 4.99/1.95  ----------------------
% 4.99/1.95  #Subsume      : 263
% 4.99/1.95  #Demod        : 14
% 4.99/1.95  #Tautology    : 94
% 4.99/1.95  #SimpNegUnit  : 0
% 4.99/1.95  #BackRed      : 0
% 4.99/1.95  
% 4.99/1.95  #Partial instantiations: 0
% 4.99/1.95  #Strategies tried      : 1
% 4.99/1.95  
% 4.99/1.95  Timing (in seconds)
% 4.99/1.95  ----------------------
% 4.99/1.95  Preprocessing        : 0.32
% 4.99/1.95  Parsing              : 0.17
% 4.99/1.95  CNF conversion       : 0.02
% 4.99/1.95  Main loop            : 0.86
% 4.99/1.95  Inferencing          : 0.31
% 4.99/1.95  Reduction            : 0.26
% 4.99/1.95  Demodulation         : 0.21
% 4.99/1.95  BG Simplification    : 0.04
% 4.99/1.95  Subsumption          : 0.20
% 4.99/1.95  Abstraction          : 0.04
% 4.99/1.95  MUC search           : 0.00
% 4.99/1.95  Cooper               : 0.00
% 4.99/1.95  Total                : 1.21
% 4.99/1.95  Index Insertion      : 0.00
% 4.99/1.95  Index Deletion       : 0.00
% 4.99/1.95  Index Matching       : 0.00
% 4.99/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
