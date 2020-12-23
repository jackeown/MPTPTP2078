%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:52 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   78 (  94 expanded)
%              Number of leaves         :   41 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 110 expanded)
%              Number of equality atoms :   37 (  47 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_87,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_81,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_85,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_79,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_55] :
      ( v1_relat_1(A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_84,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_50,plain,(
    ! [A_47] :
      ( v1_relat_1(k4_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_95,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_22,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_4'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_651,plain,(
    ! [C_120,A_121] :
      ( r2_hidden(k4_tarski(C_120,'#skF_8'(A_121,k1_relat_1(A_121),C_120)),A_121)
      | ~ r2_hidden(C_120,k1_relat_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_361,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_380,plain,(
    ! [A_22,C_87] :
      ( ~ r1_xboole_0(A_22,k1_xboole_0)
      | ~ r2_hidden(C_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_361])).

tff(c_386,plain,(
    ! [C_87] : ~ r2_hidden(C_87,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_380])).

tff(c_673,plain,(
    ! [C_122] : ~ r2_hidden(C_122,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_651,c_386])).

tff(c_689,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_673])).

tff(c_700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_689])).

tff(c_701,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_32,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_924,plain,(
    ! [A_142,B_143] : k5_xboole_0(A_142,k3_xboole_0(A_142,B_143)) = k4_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_933,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = k4_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_924])).

tff(c_936,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_933])).

tff(c_702,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,(
    ! [A_51] :
      ( k2_relat_1(k4_relat_1(A_51)) = k1_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_713,plain,(
    ! [B_125,A_126] : k2_xboole_0(B_125,A_126) = k2_xboole_0(A_126,B_125) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_729,plain,(
    ! [A_126] : k2_xboole_0(k1_xboole_0,A_126) = A_126 ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_26])).

tff(c_1390,plain,(
    ! [A_190,B_191] :
      ( k2_xboole_0(k2_relat_1(A_190),k2_relat_1(B_191)) = k2_relat_1(k2_xboole_0(A_190,B_191))
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1488,plain,(
    ! [A_195,B_196] :
      ( k4_xboole_0(k2_relat_1(A_195),k2_relat_1(k2_xboole_0(A_195,B_196))) = k1_xboole_0
      | ~ v1_relat_1(B_196)
      | ~ v1_relat_1(A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_30])).

tff(c_1503,plain,(
    ! [A_126] :
      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k2_relat_1(A_126)) = k1_xboole_0
      | ~ v1_relat_1(A_126)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_1488])).

tff(c_1519,plain,(
    ! [A_197] :
      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k2_relat_1(A_197)) = k1_xboole_0
      | ~ v1_relat_1(A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1503])).

tff(c_1574,plain,(
    ! [A_200] :
      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(A_200)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_200))
      | ~ v1_relat_1(A_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1519])).

tff(c_1586,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_1574])).

tff(c_1590,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_936,c_1586])).

tff(c_1591,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_701,c_1590])).

tff(c_1594,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_1591])).

tff(c_1598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.49  
% 3.04/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.49  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_5
% 3.04/1.49  
% 3.04/1.49  %Foreground sorts:
% 3.04/1.49  
% 3.04/1.49  
% 3.04/1.49  %Background operators:
% 3.04/1.49  
% 3.04/1.49  
% 3.04/1.49  %Foreground operators:
% 3.04/1.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.04/1.49  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.04/1.49  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.04/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.49  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.04/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.49  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.04/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.04/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.04/1.49  
% 3.16/1.51  tff(f_35, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.16/1.51  tff(f_91, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.16/1.51  tff(f_103, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.16/1.51  tff(f_120, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.16/1.51  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.51  tff(f_99, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.16/1.51  tff(f_87, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.16/1.51  tff(f_81, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.16/1.51  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.16/1.51  tff(f_85, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.16/1.51  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.16/1.51  tff(f_116, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.16/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.16/1.51  tff(f_79, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.16/1.51  tff(f_110, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 3.16/1.51  tff(f_83, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.16/1.51  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.51  tff(c_80, plain, (![A_55]: (v1_relat_1(A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.51  tff(c_84, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_80])).
% 3.16/1.51  tff(c_50, plain, (![A_47]: (v1_relat_1(k4_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.16/1.51  tff(c_58, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.16/1.51  tff(c_95, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 3.16/1.51  tff(c_22, plain, (![A_17]: (r2_hidden('#skF_4'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.51  tff(c_651, plain, (![C_120, A_121]: (r2_hidden(k4_tarski(C_120, '#skF_8'(A_121, k1_relat_1(A_121), C_120)), A_121) | ~r2_hidden(C_120, k1_relat_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.16/1.51  tff(c_34, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.51  tff(c_28, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.51  tff(c_361, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/1.51  tff(c_380, plain, (![A_22, C_87]: (~r1_xboole_0(A_22, k1_xboole_0) | ~r2_hidden(C_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_361])).
% 3.16/1.51  tff(c_386, plain, (![C_87]: (~r2_hidden(C_87, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_380])).
% 3.16/1.51  tff(c_673, plain, (![C_122]: (~r2_hidden(C_122, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_651, c_386])).
% 3.16/1.51  tff(c_689, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_673])).
% 3.16/1.51  tff(c_700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_689])).
% 3.16/1.51  tff(c_701, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.16/1.51  tff(c_32, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.51  tff(c_924, plain, (![A_142, B_143]: (k5_xboole_0(A_142, k3_xboole_0(A_142, B_143))=k4_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.51  tff(c_933, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=k4_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_924])).
% 3.16/1.51  tff(c_936, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_933])).
% 3.16/1.51  tff(c_702, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.16/1.51  tff(c_54, plain, (![A_51]: (k2_relat_1(k4_relat_1(A_51))=k1_relat_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.51  tff(c_713, plain, (![B_125, A_126]: (k2_xboole_0(B_125, A_126)=k2_xboole_0(A_126, B_125))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.51  tff(c_26, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.16/1.51  tff(c_729, plain, (![A_126]: (k2_xboole_0(k1_xboole_0, A_126)=A_126)), inference(superposition, [status(thm), theory('equality')], [c_713, c_26])).
% 3.16/1.51  tff(c_1390, plain, (![A_190, B_191]: (k2_xboole_0(k2_relat_1(A_190), k2_relat_1(B_191))=k2_relat_1(k2_xboole_0(A_190, B_191)) | ~v1_relat_1(B_191) | ~v1_relat_1(A_190))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.16/1.51  tff(c_30, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.51  tff(c_1488, plain, (![A_195, B_196]: (k4_xboole_0(k2_relat_1(A_195), k2_relat_1(k2_xboole_0(A_195, B_196)))=k1_xboole_0 | ~v1_relat_1(B_196) | ~v1_relat_1(A_195))), inference(superposition, [status(thm), theory('equality')], [c_1390, c_30])).
% 3.16/1.51  tff(c_1503, plain, (![A_126]: (k4_xboole_0(k2_relat_1(k1_xboole_0), k2_relat_1(A_126))=k1_xboole_0 | ~v1_relat_1(A_126) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_729, c_1488])).
% 3.16/1.51  tff(c_1519, plain, (![A_197]: (k4_xboole_0(k2_relat_1(k1_xboole_0), k2_relat_1(A_197))=k1_xboole_0 | ~v1_relat_1(A_197))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1503])).
% 3.16/1.51  tff(c_1574, plain, (![A_200]: (k4_xboole_0(k2_relat_1(k1_xboole_0), k1_relat_1(A_200))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_200)) | ~v1_relat_1(A_200))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1519])).
% 3.16/1.51  tff(c_1586, plain, (k4_xboole_0(k2_relat_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_702, c_1574])).
% 3.16/1.51  tff(c_1590, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_936, c_1586])).
% 3.16/1.51  tff(c_1591, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_701, c_1590])).
% 3.16/1.51  tff(c_1594, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_1591])).
% 3.16/1.51  tff(c_1598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1594])).
% 3.16/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  Inference rules
% 3.16/1.51  ----------------------
% 3.16/1.51  #Ref     : 0
% 3.16/1.51  #Sup     : 352
% 3.16/1.51  #Fact    : 0
% 3.16/1.51  #Define  : 0
% 3.16/1.51  #Split   : 1
% 3.16/1.51  #Chain   : 0
% 3.16/1.51  #Close   : 0
% 3.16/1.51  
% 3.16/1.51  Ordering : KBO
% 3.16/1.51  
% 3.16/1.51  Simplification rules
% 3.16/1.51  ----------------------
% 3.16/1.51  #Subsume      : 41
% 3.16/1.51  #Demod        : 152
% 3.16/1.51  #Tautology    : 238
% 3.16/1.51  #SimpNegUnit  : 9
% 3.16/1.51  #BackRed      : 0
% 3.16/1.51  
% 3.16/1.51  #Partial instantiations: 0
% 3.16/1.51  #Strategies tried      : 1
% 3.16/1.51  
% 3.16/1.51  Timing (in seconds)
% 3.16/1.51  ----------------------
% 3.16/1.51  Preprocessing        : 0.33
% 3.16/1.51  Parsing              : 0.17
% 3.16/1.51  CNF conversion       : 0.03
% 3.16/1.51  Main loop            : 0.41
% 3.16/1.51  Inferencing          : 0.16
% 3.16/1.51  Reduction            : 0.13
% 3.16/1.51  Demodulation         : 0.09
% 3.16/1.51  BG Simplification    : 0.02
% 3.16/1.51  Subsumption          : 0.07
% 3.16/1.51  Abstraction          : 0.02
% 3.16/1.51  MUC search           : 0.00
% 3.16/1.51  Cooper               : 0.00
% 3.16/1.51  Total                : 0.78
% 3.16/1.51  Index Insertion      : 0.00
% 3.16/1.51  Index Deletion       : 0.00
% 3.16/1.51  Index Matching       : 0.00
% 3.16/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
