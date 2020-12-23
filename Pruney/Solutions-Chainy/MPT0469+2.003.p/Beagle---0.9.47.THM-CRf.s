%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:52 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 118 expanded)
%              Number of leaves         :   38 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 164 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_7 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_116,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_83,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_75,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(c_58,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_100,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_876,plain,(
    ! [C_131,A_132] :
      ( r2_hidden(k4_tarski(C_131,'#skF_7'(A_132,k1_relat_1(A_132),C_131)),A_132)
      | ~ r2_hidden(C_131,k1_relat_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_356,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_371,plain,(
    ! [A_21,C_85] :
      ( ~ r1_xboole_0(A_21,k1_xboole_0)
      | ~ r2_hidden(C_85,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_356])).

tff(c_376,plain,(
    ! [C_85] : ~ r2_hidden(C_85,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_371])).

tff(c_898,plain,(
    ! [C_133] : ~ r2_hidden(C_133,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_876,c_376])).

tff(c_923,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6,c_898])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_933,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_923,c_12])).

tff(c_940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_933])).

tff(c_941,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_56] :
      ( v1_relat_1(A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_942,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_949,plain,(
    ! [B_137,A_138] : k2_xboole_0(B_137,A_138) = k2_xboole_0(A_138,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_965,plain,(
    ! [A_138] : k2_xboole_0(k1_xboole_0,A_138) = A_138 ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_26])).

tff(c_50,plain,(
    ! [A_46] :
      ( v1_relat_1(k4_relat_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    ! [A_50] :
      ( k2_relat_1(k4_relat_1(A_50)) = k1_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1689,plain,(
    ! [A_206,B_207] :
      ( k2_xboole_0(k2_relat_1(A_206),k2_relat_1(B_207)) = k2_relat_1(k2_xboole_0(A_206,B_207))
      | ~ v1_relat_1(B_207)
      | ~ v1_relat_1(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6920,plain,(
    ! [A_366,A_367] :
      ( k2_xboole_0(k2_relat_1(A_366),k1_relat_1(A_367)) = k2_relat_1(k2_xboole_0(A_366,k4_relat_1(A_367)))
      | ~ v1_relat_1(k4_relat_1(A_367))
      | ~ v1_relat_1(A_366)
      | ~ v1_relat_1(A_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1689])).

tff(c_6974,plain,(
    ! [A_366] :
      ( k2_relat_1(k2_xboole_0(A_366,k4_relat_1(k1_xboole_0))) = k2_xboole_0(k2_relat_1(A_366),k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_366)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_6920])).

tff(c_6984,plain,(
    ! [A_366] :
      ( k2_relat_1(k2_xboole_0(A_366,k4_relat_1(k1_xboole_0))) = k2_relat_1(A_366)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_26,c_6974])).

tff(c_7110,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_6984])).

tff(c_7113,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_7110])).

tff(c_7117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_7113])).

tff(c_7120,plain,(
    ! [A_375] :
      ( k2_relat_1(k2_xboole_0(A_375,k4_relat_1(k1_xboole_0))) = k2_relat_1(A_375)
      | ~ v1_relat_1(A_375) ) ),
    inference(splitRight,[status(thm)],[c_6984])).

tff(c_7175,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_7120])).

tff(c_7189,plain,(
    k2_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_7175])).

tff(c_7235,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7189,c_54])).

tff(c_7270,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_942,c_7235])).

tff(c_7272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_7270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.97/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.23  
% 5.97/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.23  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 5.97/2.23  
% 5.97/2.23  %Foreground sorts:
% 5.97/2.23  
% 5.97/2.23  
% 5.97/2.23  %Background operators:
% 5.97/2.23  
% 5.97/2.23  
% 5.97/2.23  %Foreground operators:
% 5.97/2.23  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.97/2.23  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.97/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.97/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.97/2.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.97/2.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.97/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.97/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.97/2.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.97/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.97/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.97/2.23  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.97/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.97/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.97/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.97/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.97/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.97/2.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.97/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.97/2.23  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.97/2.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.97/2.23  
% 5.97/2.25  tff(f_116, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.97/2.25  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.97/2.25  tff(f_95, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.97/2.25  tff(f_83, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.97/2.25  tff(f_77, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.97/2.25  tff(f_71, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.97/2.25  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.97/2.25  tff(f_35, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.97/2.25  tff(f_87, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.97/2.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.97/2.25  tff(f_75, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.97/2.25  tff(f_99, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.97/2.25  tff(f_112, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 5.97/2.25  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 5.97/2.25  tff(c_58, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.97/2.25  tff(c_100, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 5.97/2.25  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.97/2.25  tff(c_876, plain, (![C_131, A_132]: (r2_hidden(k4_tarski(C_131, '#skF_7'(A_132, k1_relat_1(A_132), C_131)), A_132) | ~r2_hidden(C_131, k1_relat_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.97/2.25  tff(c_34, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.97/2.25  tff(c_28, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.97/2.25  tff(c_356, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.97/2.25  tff(c_371, plain, (![A_21, C_85]: (~r1_xboole_0(A_21, k1_xboole_0) | ~r2_hidden(C_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_356])).
% 5.97/2.25  tff(c_376, plain, (![C_85]: (~r2_hidden(C_85, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_371])).
% 5.97/2.25  tff(c_898, plain, (![C_133]: (~r2_hidden(C_133, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_876, c_376])).
% 5.97/2.25  tff(c_923, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_898])).
% 5.97/2.25  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.97/2.25  tff(c_933, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_923, c_12])).
% 5.97/2.25  tff(c_940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_933])).
% 5.97/2.25  tff(c_941, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 5.97/2.25  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.97/2.25  tff(c_95, plain, (![A_56]: (v1_relat_1(A_56) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.97/2.25  tff(c_99, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_95])).
% 5.97/2.25  tff(c_942, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 5.97/2.25  tff(c_949, plain, (![B_137, A_138]: (k2_xboole_0(B_137, A_138)=k2_xboole_0(A_138, B_137))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.97/2.25  tff(c_26, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.97/2.25  tff(c_965, plain, (![A_138]: (k2_xboole_0(k1_xboole_0, A_138)=A_138)), inference(superposition, [status(thm), theory('equality')], [c_949, c_26])).
% 5.97/2.25  tff(c_50, plain, (![A_46]: (v1_relat_1(k4_relat_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.97/2.25  tff(c_54, plain, (![A_50]: (k2_relat_1(k4_relat_1(A_50))=k1_relat_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.97/2.25  tff(c_1689, plain, (![A_206, B_207]: (k2_xboole_0(k2_relat_1(A_206), k2_relat_1(B_207))=k2_relat_1(k2_xboole_0(A_206, B_207)) | ~v1_relat_1(B_207) | ~v1_relat_1(A_206))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.97/2.25  tff(c_6920, plain, (![A_366, A_367]: (k2_xboole_0(k2_relat_1(A_366), k1_relat_1(A_367))=k2_relat_1(k2_xboole_0(A_366, k4_relat_1(A_367))) | ~v1_relat_1(k4_relat_1(A_367)) | ~v1_relat_1(A_366) | ~v1_relat_1(A_367))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1689])).
% 5.97/2.25  tff(c_6974, plain, (![A_366]: (k2_relat_1(k2_xboole_0(A_366, k4_relat_1(k1_xboole_0)))=k2_xboole_0(k2_relat_1(A_366), k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_366) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_942, c_6920])).
% 5.97/2.25  tff(c_6984, plain, (![A_366]: (k2_relat_1(k2_xboole_0(A_366, k4_relat_1(k1_xboole_0)))=k2_relat_1(A_366) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_366))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_26, c_6974])).
% 5.97/2.25  tff(c_7110, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_6984])).
% 5.97/2.25  tff(c_7113, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_7110])).
% 5.97/2.25  tff(c_7117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_7113])).
% 5.97/2.25  tff(c_7120, plain, (![A_375]: (k2_relat_1(k2_xboole_0(A_375, k4_relat_1(k1_xboole_0)))=k2_relat_1(A_375) | ~v1_relat_1(A_375))), inference(splitRight, [status(thm)], [c_6984])).
% 5.97/2.25  tff(c_7175, plain, (k2_relat_1(k4_relat_1(k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_965, c_7120])).
% 5.97/2.25  tff(c_7189, plain, (k2_relat_1(k4_relat_1(k1_xboole_0))=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_7175])).
% 5.97/2.25  tff(c_7235, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7189, c_54])).
% 5.97/2.25  tff(c_7270, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_942, c_7235])).
% 5.97/2.25  tff(c_7272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_941, c_7270])).
% 5.97/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.25  
% 5.97/2.25  Inference rules
% 5.97/2.25  ----------------------
% 5.97/2.25  #Ref     : 0
% 5.97/2.25  #Sup     : 1755
% 5.97/2.25  #Fact    : 0
% 5.97/2.25  #Define  : 0
% 5.97/2.25  #Split   : 2
% 5.97/2.25  #Chain   : 0
% 5.97/2.25  #Close   : 0
% 5.97/2.25  
% 5.97/2.25  Ordering : KBO
% 5.97/2.25  
% 5.97/2.25  Simplification rules
% 5.97/2.25  ----------------------
% 5.97/2.25  #Subsume      : 278
% 5.97/2.25  #Demod        : 1635
% 5.97/2.25  #Tautology    : 1070
% 5.97/2.25  #SimpNegUnit  : 26
% 5.97/2.25  #BackRed      : 0
% 5.97/2.25  
% 5.97/2.25  #Partial instantiations: 0
% 5.97/2.25  #Strategies tried      : 1
% 5.97/2.25  
% 5.97/2.25  Timing (in seconds)
% 5.97/2.25  ----------------------
% 5.97/2.25  Preprocessing        : 0.32
% 5.97/2.25  Parsing              : 0.17
% 5.97/2.25  CNF conversion       : 0.02
% 5.97/2.25  Main loop            : 1.12
% 5.97/2.25  Inferencing          : 0.37
% 5.97/2.25  Reduction            : 0.36
% 5.97/2.25  Demodulation         : 0.26
% 5.97/2.25  BG Simplification    : 0.04
% 5.97/2.25  Subsumption          : 0.28
% 5.97/2.25  Abstraction          : 0.05
% 5.97/2.25  MUC search           : 0.00
% 5.97/2.25  Cooper               : 0.00
% 5.97/2.25  Total                : 1.48
% 5.97/2.25  Index Insertion      : 0.00
% 5.97/2.25  Index Deletion       : 0.00
% 5.97/2.25  Index Matching       : 0.00
% 5.97/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
