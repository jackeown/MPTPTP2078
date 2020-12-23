%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:11 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 109 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 168 expanded)
%              Number of equality atoms :   38 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_68,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_35] :
      ( v1_relat_1(A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(k5_relat_1(A_25,B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_40,B_41] :
      ( v1_xboole_0(k2_zfmisc_1(A_40,B_41))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_133,plain,(
    ! [A_51,B_52] :
      ( k2_zfmisc_1(A_51,B_52) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_142,plain,(
    ! [B_52] : k2_zfmisc_1(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_133])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_598,plain,(
    ! [A_88,B_89] :
      ( k1_relat_1(k5_relat_1(A_88,B_89)) = k1_relat_1(A_88)
      | ~ r1_tarski(k2_relat_1(A_88),k1_relat_1(B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_607,plain,(
    ! [B_89] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_89)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_598])).

tff(c_628,plain,(
    ! [B_90] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_90)) = k1_xboole_0
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8,c_36,c_607])).

tff(c_28,plain,(
    ! [A_27] :
      ( k3_xboole_0(A_27,k2_zfmisc_1(k1_relat_1(A_27),k2_relat_1(A_27))) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_640,plain,(
    ! [B_90] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_90),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_90)))) = k5_relat_1(k1_xboole_0,B_90)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_28])).

tff(c_796,plain,(
    ! [B_97] :
      ( k5_relat_1(k1_xboole_0,B_97) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_142,c_640])).

tff(c_803,plain,(
    ! [B_26] :
      ( k5_relat_1(k1_xboole_0,B_26) = k1_xboole_0
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_796])).

tff(c_809,plain,(
    ! [B_98] :
      ( k5_relat_1(k1_xboole_0,B_98) = k1_xboole_0
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_803])).

tff(c_824,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_809])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_824])).

tff(c_834,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_840,plain,(
    ! [A_99,B_100] :
      ( v1_xboole_0(k2_zfmisc_1(A_99,B_100))
      | ~ v1_xboole_0(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_858,plain,(
    ! [A_103,B_104] :
      ( k2_zfmisc_1(A_103,B_104) = k1_xboole_0
      | ~ v1_xboole_0(B_104) ) ),
    inference(resolution,[status(thm)],[c_840,c_4])).

tff(c_867,plain,(
    ! [A_103] : k2_zfmisc_1(A_103,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_858])).

tff(c_1304,plain,(
    ! [B_144,A_145] :
      ( k2_relat_1(k5_relat_1(B_144,A_145)) = k2_relat_1(A_145)
      | ~ r1_tarski(k1_relat_1(A_145),k2_relat_1(B_144))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1307,plain,(
    ! [B_144] :
      ( k2_relat_1(k5_relat_1(B_144,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_144))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1304])).

tff(c_1326,plain,(
    ! [B_148] :
      ( k2_relat_1(k5_relat_1(B_148,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8,c_34,c_1307])).

tff(c_1338,plain,(
    ! [B_148] :
      ( k3_xboole_0(k5_relat_1(B_148,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_148,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_148,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_148,k1_xboole_0))
      | ~ v1_relat_1(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_28])).

tff(c_1373,plain,(
    ! [B_150] :
      ( k5_relat_1(B_150,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_150,k1_xboole_0))
      | ~ v1_relat_1(B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_867,c_1338])).

tff(c_1377,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_1373])).

tff(c_1416,plain,(
    ! [A_153] :
      ( k5_relat_1(A_153,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1377])).

tff(c_1431,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1416])).

tff(c_1439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_1431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:11:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.26/1.50  
% 3.26/1.50  %Foreground sorts:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Background operators:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Foreground operators:
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.26/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.26/1.50  
% 3.26/1.52  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.26/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.26/1.52  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.26/1.52  tff(f_62, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.26/1.52  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.26/1.52  tff(f_50, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.26/1.52  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.26/1.52  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.52  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.26/1.52  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.26/1.52  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.26/1.52  tff(f_46, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.26/1.52  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.26/1.52  tff(c_38, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.52  tff(c_68, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.26/1.52  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.26/1.52  tff(c_50, plain, (![A_35]: (v1_relat_1(A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.52  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 3.26/1.52  tff(c_26, plain, (![A_25, B_26]: (v1_relat_1(k5_relat_1(A_25, B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.26/1.52  tff(c_6, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.52  tff(c_78, plain, (![A_40, B_41]: (v1_xboole_0(k2_zfmisc_1(A_40, B_41)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.52  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.26/1.52  tff(c_133, plain, (![A_51, B_52]: (k2_zfmisc_1(A_51, B_52)=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_78, c_4])).
% 3.26/1.52  tff(c_142, plain, (![B_52]: (k2_zfmisc_1(k1_xboole_0, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_133])).
% 3.26/1.52  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.26/1.52  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.26/1.52  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.26/1.52  tff(c_598, plain, (![A_88, B_89]: (k1_relat_1(k5_relat_1(A_88, B_89))=k1_relat_1(A_88) | ~r1_tarski(k2_relat_1(A_88), k1_relat_1(B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.52  tff(c_607, plain, (![B_89]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_89))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_598])).
% 3.26/1.52  tff(c_628, plain, (![B_90]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_90))=k1_xboole_0 | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8, c_36, c_607])).
% 3.26/1.52  tff(c_28, plain, (![A_27]: (k3_xboole_0(A_27, k2_zfmisc_1(k1_relat_1(A_27), k2_relat_1(A_27)))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.52  tff(c_640, plain, (![B_90]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_90), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_90))))=k5_relat_1(k1_xboole_0, B_90) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_90)) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_628, c_28])).
% 3.26/1.52  tff(c_796, plain, (![B_97]: (k5_relat_1(k1_xboole_0, B_97)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_97)) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_142, c_640])).
% 3.26/1.52  tff(c_803, plain, (![B_26]: (k5_relat_1(k1_xboole_0, B_26)=k1_xboole_0 | ~v1_relat_1(B_26) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_796])).
% 3.26/1.52  tff(c_809, plain, (![B_98]: (k5_relat_1(k1_xboole_0, B_98)=k1_xboole_0 | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_803])).
% 3.26/1.52  tff(c_824, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_809])).
% 3.26/1.52  tff(c_833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_824])).
% 3.26/1.52  tff(c_834, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.26/1.52  tff(c_840, plain, (![A_99, B_100]: (v1_xboole_0(k2_zfmisc_1(A_99, B_100)) | ~v1_xboole_0(B_100))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.26/1.52  tff(c_858, plain, (![A_103, B_104]: (k2_zfmisc_1(A_103, B_104)=k1_xboole_0 | ~v1_xboole_0(B_104))), inference(resolution, [status(thm)], [c_840, c_4])).
% 3.26/1.52  tff(c_867, plain, (![A_103]: (k2_zfmisc_1(A_103, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_858])).
% 3.26/1.52  tff(c_1304, plain, (![B_144, A_145]: (k2_relat_1(k5_relat_1(B_144, A_145))=k2_relat_1(A_145) | ~r1_tarski(k1_relat_1(A_145), k2_relat_1(B_144)) | ~v1_relat_1(B_144) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.26/1.52  tff(c_1307, plain, (![B_144]: (k2_relat_1(k5_relat_1(B_144, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_144)) | ~v1_relat_1(B_144) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1304])).
% 3.26/1.52  tff(c_1326, plain, (![B_148]: (k2_relat_1(k5_relat_1(B_148, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8, c_34, c_1307])).
% 3.26/1.52  tff(c_1338, plain, (![B_148]: (k3_xboole_0(k5_relat_1(B_148, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_148, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_148, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_148, k1_xboole_0)) | ~v1_relat_1(B_148))), inference(superposition, [status(thm), theory('equality')], [c_1326, c_28])).
% 3.26/1.52  tff(c_1373, plain, (![B_150]: (k5_relat_1(B_150, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_150, k1_xboole_0)) | ~v1_relat_1(B_150))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_867, c_1338])).
% 3.26/1.52  tff(c_1377, plain, (![A_25]: (k5_relat_1(A_25, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_26, c_1373])).
% 3.26/1.52  tff(c_1416, plain, (![A_153]: (k5_relat_1(A_153, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1377])).
% 3.26/1.52  tff(c_1431, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_1416])).
% 3.26/1.52  tff(c_1439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_834, c_1431])).
% 3.26/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.52  
% 3.26/1.52  Inference rules
% 3.26/1.52  ----------------------
% 3.26/1.52  #Ref     : 0
% 3.26/1.52  #Sup     : 328
% 3.26/1.52  #Fact    : 0
% 3.26/1.52  #Define  : 0
% 3.26/1.52  #Split   : 1
% 3.26/1.52  #Chain   : 0
% 3.26/1.52  #Close   : 0
% 3.26/1.52  
% 3.26/1.52  Ordering : KBO
% 3.26/1.52  
% 3.26/1.52  Simplification rules
% 3.26/1.52  ----------------------
% 3.26/1.52  #Subsume      : 3
% 3.26/1.52  #Demod        : 236
% 3.26/1.52  #Tautology    : 266
% 3.26/1.52  #SimpNegUnit  : 2
% 3.26/1.52  #BackRed      : 0
% 3.26/1.52  
% 3.26/1.52  #Partial instantiations: 0
% 3.26/1.52  #Strategies tried      : 1
% 3.26/1.52  
% 3.26/1.52  Timing (in seconds)
% 3.26/1.52  ----------------------
% 3.26/1.52  Preprocessing        : 0.32
% 3.26/1.52  Parsing              : 0.17
% 3.26/1.52  CNF conversion       : 0.02
% 3.26/1.52  Main loop            : 0.42
% 3.26/1.52  Inferencing          : 0.17
% 3.26/1.52  Reduction            : 0.13
% 3.26/1.52  Demodulation         : 0.09
% 3.26/1.52  BG Simplification    : 0.02
% 3.26/1.52  Subsumption          : 0.07
% 3.26/1.52  Abstraction          : 0.03
% 3.26/1.52  MUC search           : 0.00
% 3.26/1.52  Cooper               : 0.00
% 3.26/1.52  Total                : 0.78
% 3.26/1.52  Index Insertion      : 0.00
% 3.26/1.52  Index Deletion       : 0.00
% 3.26/1.52  Index Matching       : 0.00
% 3.26/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
