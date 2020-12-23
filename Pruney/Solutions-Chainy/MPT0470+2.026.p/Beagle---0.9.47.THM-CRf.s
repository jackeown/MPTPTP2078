%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 111 expanded)
%              Number of leaves         :   33 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 172 expanded)
%              Number of equality atoms :   38 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_44,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_69,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    ! [A_39] :
      ( v1_relat_1(A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( v1_relat_1(k5_relat_1(A_27,B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [A_43,B_44] :
      ( v1_xboole_0(k2_zfmisc_1(A_43,B_44))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_136,plain,(
    ! [A_52,B_53] :
      ( k2_zfmisc_1(A_52,B_53) = k1_xboole_0
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_145,plain,(
    ! [B_53] : k2_zfmisc_1(k1_xboole_0,B_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_136])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_849,plain,(
    ! [A_101,B_102] :
      ( k1_relat_1(k5_relat_1(A_101,B_102)) = k1_relat_1(A_101)
      | ~ r1_tarski(k2_relat_1(A_101),k1_relat_1(B_102))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_858,plain,(
    ! [B_102] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_102)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_102))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_849])).

tff(c_865,plain,(
    ! [B_103] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_103)) = k1_xboole_0
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14,c_42,c_858])).

tff(c_34,plain,(
    ! [A_29] :
      ( k3_xboole_0(A_29,k2_zfmisc_1(k1_relat_1(A_29),k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_874,plain,(
    ! [B_103] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_103),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_103)))) = k5_relat_1(k1_xboole_0,B_103)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_103))
      | ~ v1_relat_1(B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_34])).

tff(c_886,plain,(
    ! [B_104] :
      ( k5_relat_1(k1_xboole_0,B_104) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_145,c_874])).

tff(c_893,plain,(
    ! [B_28] :
      ( k5_relat_1(k1_xboole_0,B_28) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_886])).

tff(c_899,plain,(
    ! [B_105] :
      ( k5_relat_1(k1_xboole_0,B_105) = k1_xboole_0
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_893])).

tff(c_914,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_899])).

tff(c_923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_914])).

tff(c_924,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_946,plain,(
    ! [A_109,B_110] :
      ( v1_xboole_0(k2_zfmisc_1(A_109,B_110))
      | ~ v1_xboole_0(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1001,plain,(
    ! [A_120,B_121] :
      ( k2_zfmisc_1(A_120,B_121) = k1_xboole_0
      | ~ v1_xboole_0(B_121) ) ),
    inference(resolution,[status(thm)],[c_946,c_4])).

tff(c_1010,plain,(
    ! [A_120] : k2_zfmisc_1(A_120,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1001])).

tff(c_1406,plain,(
    ! [A_146,B_147] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_146,B_147)),k2_relat_1(B_147))
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1414,plain,(
    ! [A_146] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_146,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1406])).

tff(c_1420,plain,(
    ! [A_148] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_148,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1414])).

tff(c_1053,plain,(
    ! [B_125,A_126] :
      ( B_125 = A_126
      | ~ r1_tarski(B_125,A_126)
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1062,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_1053])).

tff(c_1430,plain,(
    ! [A_149] :
      ( k2_relat_1(k5_relat_1(A_149,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_1420,c_1062])).

tff(c_1445,plain,(
    ! [A_149] :
      ( k3_xboole_0(k5_relat_1(A_149,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_149,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_149,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_149,k1_xboole_0))
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_34])).

tff(c_1455,plain,(
    ! [A_150] :
      ( k5_relat_1(A_150,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_150,k1_xboole_0))
      | ~ v1_relat_1(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1010,c_1445])).

tff(c_1459,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_1455])).

tff(c_1472,plain,(
    ! [A_155] :
      ( k5_relat_1(A_155,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1459])).

tff(c_1487,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1472])).

tff(c_1495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_924,c_1487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.49  
% 3.11/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.49  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.11/1.49  
% 3.11/1.49  %Foreground sorts:
% 3.11/1.49  
% 3.11/1.49  
% 3.11/1.49  %Background operators:
% 3.11/1.49  
% 3.11/1.49  
% 3.11/1.49  %Foreground operators:
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.11/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.11/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.11/1.49  
% 3.19/1.50  tff(f_98, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.19/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.19/1.50  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.19/1.50  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.19/1.50  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.19/1.50  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.19/1.50  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.19/1.50  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.19/1.50  tff(f_91, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.19/1.50  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.19/1.50  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.19/1.50  tff(f_52, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.19/1.50  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.19/1.50  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.50  tff(c_44, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.19/1.50  tff(c_69, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.19/1.50  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.19/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.19/1.50  tff(c_64, plain, (![A_39]: (v1_relat_1(A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.50  tff(c_68, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_64])).
% 3.19/1.50  tff(c_32, plain, (![A_27, B_28]: (v1_relat_1(k5_relat_1(A_27, B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.19/1.50  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.19/1.50  tff(c_86, plain, (![A_43, B_44]: (v1_xboole_0(k2_zfmisc_1(A_43, B_44)) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.19/1.50  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.19/1.50  tff(c_136, plain, (![A_52, B_53]: (k2_zfmisc_1(A_52, B_53)=k1_xboole_0 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_86, c_4])).
% 3.19/1.50  tff(c_145, plain, (![B_53]: (k2_zfmisc_1(k1_xboole_0, B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_136])).
% 3.19/1.50  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.19/1.50  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.50  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.50  tff(c_849, plain, (![A_101, B_102]: (k1_relat_1(k5_relat_1(A_101, B_102))=k1_relat_1(A_101) | ~r1_tarski(k2_relat_1(A_101), k1_relat_1(B_102)) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.50  tff(c_858, plain, (![B_102]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_102))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_102)) | ~v1_relat_1(B_102) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_849])).
% 3.19/1.50  tff(c_865, plain, (![B_103]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_103))=k1_xboole_0 | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14, c_42, c_858])).
% 3.19/1.50  tff(c_34, plain, (![A_29]: (k3_xboole_0(A_29, k2_zfmisc_1(k1_relat_1(A_29), k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.19/1.50  tff(c_874, plain, (![B_103]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_103), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_103))))=k5_relat_1(k1_xboole_0, B_103) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_103)) | ~v1_relat_1(B_103))), inference(superposition, [status(thm), theory('equality')], [c_865, c_34])).
% 3.19/1.50  tff(c_886, plain, (![B_104]: (k5_relat_1(k1_xboole_0, B_104)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_104)) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_145, c_874])).
% 3.19/1.50  tff(c_893, plain, (![B_28]: (k5_relat_1(k1_xboole_0, B_28)=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_886])).
% 3.19/1.50  tff(c_899, plain, (![B_105]: (k5_relat_1(k1_xboole_0, B_105)=k1_xboole_0 | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_893])).
% 3.19/1.50  tff(c_914, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_899])).
% 3.19/1.50  tff(c_923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_914])).
% 3.19/1.50  tff(c_924, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.19/1.50  tff(c_946, plain, (![A_109, B_110]: (v1_xboole_0(k2_zfmisc_1(A_109, B_110)) | ~v1_xboole_0(B_110))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.19/1.50  tff(c_1001, plain, (![A_120, B_121]: (k2_zfmisc_1(A_120, B_121)=k1_xboole_0 | ~v1_xboole_0(B_121))), inference(resolution, [status(thm)], [c_946, c_4])).
% 3.19/1.50  tff(c_1010, plain, (![A_120]: (k2_zfmisc_1(A_120, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1001])).
% 3.19/1.50  tff(c_1406, plain, (![A_146, B_147]: (r1_tarski(k2_relat_1(k5_relat_1(A_146, B_147)), k2_relat_1(B_147)) | ~v1_relat_1(B_147) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.19/1.50  tff(c_1414, plain, (![A_146]: (r1_tarski(k2_relat_1(k5_relat_1(A_146, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_146))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1406])).
% 3.19/1.50  tff(c_1420, plain, (![A_148]: (r1_tarski(k2_relat_1(k5_relat_1(A_148, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1414])).
% 3.19/1.50  tff(c_1053, plain, (![B_125, A_126]: (B_125=A_126 | ~r1_tarski(B_125, A_126) | ~r1_tarski(A_126, B_125))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.19/1.50  tff(c_1062, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1053])).
% 3.19/1.50  tff(c_1430, plain, (![A_149]: (k2_relat_1(k5_relat_1(A_149, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_1420, c_1062])).
% 3.19/1.50  tff(c_1445, plain, (![A_149]: (k3_xboole_0(k5_relat_1(A_149, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_149, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_149, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_149, k1_xboole_0)) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_34])).
% 3.19/1.50  tff(c_1455, plain, (![A_150]: (k5_relat_1(A_150, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_150, k1_xboole_0)) | ~v1_relat_1(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1010, c_1445])).
% 3.19/1.50  tff(c_1459, plain, (![A_27]: (k5_relat_1(A_27, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_32, c_1455])).
% 3.19/1.50  tff(c_1472, plain, (![A_155]: (k5_relat_1(A_155, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1459])).
% 3.19/1.50  tff(c_1487, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1472])).
% 3.19/1.50  tff(c_1495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_924, c_1487])).
% 3.19/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  Inference rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Ref     : 0
% 3.19/1.50  #Sup     : 337
% 3.19/1.50  #Fact    : 0
% 3.19/1.50  #Define  : 0
% 3.19/1.50  #Split   : 1
% 3.19/1.50  #Chain   : 0
% 3.19/1.50  #Close   : 0
% 3.19/1.50  
% 3.19/1.50  Ordering : KBO
% 3.19/1.50  
% 3.19/1.50  Simplification rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Subsume      : 5
% 3.19/1.50  #Demod        : 248
% 3.19/1.50  #Tautology    : 281
% 3.19/1.50  #SimpNegUnit  : 2
% 3.19/1.50  #BackRed      : 0
% 3.19/1.50  
% 3.19/1.50  #Partial instantiations: 0
% 3.19/1.50  #Strategies tried      : 1
% 3.19/1.50  
% 3.19/1.50  Timing (in seconds)
% 3.19/1.50  ----------------------
% 3.19/1.51  Preprocessing        : 0.33
% 3.19/1.51  Parsing              : 0.18
% 3.19/1.51  CNF conversion       : 0.02
% 3.19/1.51  Main loop            : 0.37
% 3.19/1.51  Inferencing          : 0.14
% 3.19/1.51  Reduction            : 0.11
% 3.19/1.51  Demodulation         : 0.08
% 3.19/1.51  BG Simplification    : 0.02
% 3.19/1.51  Subsumption          : 0.07
% 3.19/1.51  Abstraction          : 0.02
% 3.19/1.51  MUC search           : 0.00
% 3.19/1.51  Cooper               : 0.00
% 3.19/1.51  Total                : 0.74
% 3.19/1.51  Index Insertion      : 0.00
% 3.19/1.51  Index Deletion       : 0.00
% 3.19/1.51  Index Matching       : 0.00
% 3.19/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
