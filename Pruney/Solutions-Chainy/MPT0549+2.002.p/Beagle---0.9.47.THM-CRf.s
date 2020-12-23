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
% DateTime   : Thu Dec  3 10:00:48 EST 2020

% Result     : Theorem 30.13s
% Output     : CNFRefutation 30.24s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 100 expanded)
%              Number of leaves         :   40 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 152 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_95,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_70,plain,
    ( k9_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_177,plain,(
    r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11')
    | k9_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_200,plain,(
    k9_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_64])).

tff(c_62,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_490,plain,(
    ! [B_136,A_137] :
      ( k7_relat_1(B_136,A_137) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_136),A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_505,plain,
    ( k7_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_177,c_490])).

tff(c_514,plain,(
    k7_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_505])).

tff(c_52,plain,(
    ! [B_81,A_80] :
      ( k2_relat_1(k7_relat_1(B_81,A_80)) = k9_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_520,plain,
    ( k9_relat_1('#skF_12','#skF_11') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_52])).

tff(c_524,plain,(
    k9_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_520])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_524])).

tff(c_528,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_538,plain,(
    ! [A_140,B_141] : k5_xboole_0(A_140,k3_xboole_0(A_140,B_141)) = k4_xboole_0(A_140,B_141) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_556,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k4_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_538])).

tff(c_561,plain,(
    ! [A_142] : k4_xboole_0(A_142,k1_xboole_0) = A_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_556])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_567,plain,(
    ! [A_142] : r1_xboole_0(A_142,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_20])).

tff(c_596,plain,(
    ! [A_148,B_149,C_150] :
      ( ~ r1_xboole_0(A_148,B_149)
      | ~ r2_hidden(C_150,k3_xboole_0(A_148,B_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_616,plain,(
    ! [A_15,C_150] :
      ( ~ r1_xboole_0(A_15,k1_xboole_0)
      | ~ r2_hidden(C_150,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_596])).

tff(c_622,plain,(
    ! [C_150] : ~ r2_hidden(C_150,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_616])).

tff(c_527,plain,(
    k9_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_40,plain,(
    ! [C_76,A_61] :
      ( r2_hidden(k4_tarski(C_76,'#skF_10'(A_61,k1_relat_1(A_61),C_76)),A_61)
      | ~ r2_hidden(C_76,k1_relat_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1116,plain,(
    ! [D_213,A_214,B_215,E_216] :
      ( r2_hidden(D_213,k9_relat_1(A_214,B_215))
      | ~ r2_hidden(E_216,B_215)
      | ~ r2_hidden(k4_tarski(E_216,D_213),A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6921,plain,(
    ! [D_384,A_385,A_386,B_387] :
      ( r2_hidden(D_384,k9_relat_1(A_385,A_386))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_386,B_387),D_384),A_385)
      | ~ v1_relat_1(A_385)
      | r1_xboole_0(A_386,B_387) ) ),
    inference(resolution,[status(thm)],[c_8,c_1116])).

tff(c_110217,plain,(
    ! [A_1536,A_1537,B_1538] :
      ( r2_hidden('#skF_10'(A_1536,k1_relat_1(A_1536),'#skF_1'(A_1537,B_1538)),k9_relat_1(A_1536,A_1537))
      | ~ v1_relat_1(A_1536)
      | r1_xboole_0(A_1537,B_1538)
      | ~ r2_hidden('#skF_1'(A_1537,B_1538),k1_relat_1(A_1536)) ) ),
    inference(resolution,[status(thm)],[c_40,c_6921])).

tff(c_110492,plain,(
    ! [B_1538] :
      ( r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_12'),'#skF_1'('#skF_11',B_1538)),k1_xboole_0)
      | ~ v1_relat_1('#skF_12')
      | r1_xboole_0('#skF_11',B_1538)
      | ~ r2_hidden('#skF_1'('#skF_11',B_1538),k1_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_110217])).

tff(c_110540,plain,(
    ! [B_1538] :
      ( r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_12'),'#skF_1'('#skF_11',B_1538)),k1_xboole_0)
      | r1_xboole_0('#skF_11',B_1538)
      | ~ r2_hidden('#skF_1'('#skF_11',B_1538),k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_110492])).

tff(c_110543,plain,(
    ! [B_1539] :
      ( r1_xboole_0('#skF_11',B_1539)
      | ~ r2_hidden('#skF_1'('#skF_11',B_1539),k1_relat_1('#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_622,c_110540])).

tff(c_110548,plain,(
    r1_xboole_0('#skF_11',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_6,c_110543])).

tff(c_830,plain,(
    ! [A_182,B_183] :
      ( r2_hidden('#skF_2'(A_182,B_183),k3_xboole_0(A_182,B_183))
      | r1_xboole_0(A_182,B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_610,plain,(
    ! [A_1,B_2,C_150] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_150,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_596])).

tff(c_849,plain,(
    ! [B_183,A_182] :
      ( ~ r1_xboole_0(B_183,A_182)
      | r1_xboole_0(A_182,B_183) ) ),
    inference(resolution,[status(thm)],[c_830,c_610])).

tff(c_110600,plain,(
    r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_110548,c_849])).

tff(c_110639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_110600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.13/22.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.13/22.14  
% 30.13/22.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.13/22.14  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10
% 30.13/22.14  
% 30.13/22.14  %Foreground sorts:
% 30.13/22.14  
% 30.13/22.14  
% 30.13/22.14  %Background operators:
% 30.13/22.14  
% 30.13/22.14  
% 30.13/22.14  %Foreground operators:
% 30.13/22.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.13/22.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.13/22.14  tff('#skF_11', type, '#skF_11': $i).
% 30.13/22.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.13/22.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 30.13/22.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 30.13/22.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.13/22.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 30.13/22.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 30.13/22.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.13/22.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 30.13/22.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 30.13/22.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 30.13/22.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 30.13/22.14  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 30.13/22.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.13/22.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.13/22.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 30.13/22.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.13/22.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 30.13/22.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 30.13/22.14  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 30.13/22.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 30.13/22.14  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 30.13/22.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.13/22.14  tff('#skF_12', type, '#skF_12': $i).
% 30.13/22.14  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 30.13/22.14  
% 30.24/22.16  tff(f_108, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 30.24/22.16  tff(f_95, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 30.24/22.16  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 30.24/22.16  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 30.24/22.16  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 30.24/22.16  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 30.24/22.16  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 30.24/22.16  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 30.24/22.16  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 30.24/22.16  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 30.24/22.16  tff(f_88, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 30.24/22.16  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 30.24/22.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 30.24/22.16  tff(c_70, plain, (k9_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_108])).
% 30.24/22.16  tff(c_177, plain, (r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(splitLeft, [status(thm)], [c_70])).
% 30.24/22.16  tff(c_64, plain, (~r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11') | k9_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 30.24/22.16  tff(c_200, plain, (k9_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_177, c_64])).
% 30.24/22.16  tff(c_62, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_108])).
% 30.24/22.16  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 30.24/22.16  tff(c_490, plain, (![B_136, A_137]: (k7_relat_1(B_136, A_137)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_136), A_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_101])).
% 30.24/22.16  tff(c_505, plain, (k7_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_177, c_490])).
% 30.24/22.16  tff(c_514, plain, (k7_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_505])).
% 30.24/22.16  tff(c_52, plain, (![B_81, A_80]: (k2_relat_1(k7_relat_1(B_81, A_80))=k9_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.24/22.16  tff(c_520, plain, (k9_relat_1('#skF_12', '#skF_11')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_514, c_52])).
% 30.24/22.16  tff(c_524, plain, (k9_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_520])).
% 30.24/22.16  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_524])).
% 30.24/22.16  tff(c_528, plain, (~r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(splitRight, [status(thm)], [c_70])).
% 30.24/22.16  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.24/22.16  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.24/22.16  tff(c_16, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 30.24/22.16  tff(c_538, plain, (![A_140, B_141]: (k5_xboole_0(A_140, k3_xboole_0(A_140, B_141))=k4_xboole_0(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_61])).
% 30.24/22.16  tff(c_556, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k4_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_538])).
% 30.24/22.16  tff(c_561, plain, (![A_142]: (k4_xboole_0(A_142, k1_xboole_0)=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_556])).
% 30.24/22.16  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 30.24/22.16  tff(c_567, plain, (![A_142]: (r1_xboole_0(A_142, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_561, c_20])).
% 30.24/22.16  tff(c_596, plain, (![A_148, B_149, C_150]: (~r1_xboole_0(A_148, B_149) | ~r2_hidden(C_150, k3_xboole_0(A_148, B_149)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 30.24/22.16  tff(c_616, plain, (![A_15, C_150]: (~r1_xboole_0(A_15, k1_xboole_0) | ~r2_hidden(C_150, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_596])).
% 30.24/22.16  tff(c_622, plain, (![C_150]: (~r2_hidden(C_150, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_616])).
% 30.24/22.16  tff(c_527, plain, (k9_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 30.24/22.16  tff(c_40, plain, (![C_76, A_61]: (r2_hidden(k4_tarski(C_76, '#skF_10'(A_61, k1_relat_1(A_61), C_76)), A_61) | ~r2_hidden(C_76, k1_relat_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 30.24/22.16  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.24/22.16  tff(c_1116, plain, (![D_213, A_214, B_215, E_216]: (r2_hidden(D_213, k9_relat_1(A_214, B_215)) | ~r2_hidden(E_216, B_215) | ~r2_hidden(k4_tarski(E_216, D_213), A_214) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_80])).
% 30.24/22.16  tff(c_6921, plain, (![D_384, A_385, A_386, B_387]: (r2_hidden(D_384, k9_relat_1(A_385, A_386)) | ~r2_hidden(k4_tarski('#skF_1'(A_386, B_387), D_384), A_385) | ~v1_relat_1(A_385) | r1_xboole_0(A_386, B_387))), inference(resolution, [status(thm)], [c_8, c_1116])).
% 30.24/22.16  tff(c_110217, plain, (![A_1536, A_1537, B_1538]: (r2_hidden('#skF_10'(A_1536, k1_relat_1(A_1536), '#skF_1'(A_1537, B_1538)), k9_relat_1(A_1536, A_1537)) | ~v1_relat_1(A_1536) | r1_xboole_0(A_1537, B_1538) | ~r2_hidden('#skF_1'(A_1537, B_1538), k1_relat_1(A_1536)))), inference(resolution, [status(thm)], [c_40, c_6921])).
% 30.24/22.16  tff(c_110492, plain, (![B_1538]: (r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_12'), '#skF_1'('#skF_11', B_1538)), k1_xboole_0) | ~v1_relat_1('#skF_12') | r1_xboole_0('#skF_11', B_1538) | ~r2_hidden('#skF_1'('#skF_11', B_1538), k1_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_527, c_110217])).
% 30.24/22.16  tff(c_110540, plain, (![B_1538]: (r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_12'), '#skF_1'('#skF_11', B_1538)), k1_xboole_0) | r1_xboole_0('#skF_11', B_1538) | ~r2_hidden('#skF_1'('#skF_11', B_1538), k1_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_110492])).
% 30.24/22.16  tff(c_110543, plain, (![B_1539]: (r1_xboole_0('#skF_11', B_1539) | ~r2_hidden('#skF_1'('#skF_11', B_1539), k1_relat_1('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_622, c_110540])).
% 30.24/22.16  tff(c_110548, plain, (r1_xboole_0('#skF_11', k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_6, c_110543])).
% 30.24/22.16  tff(c_830, plain, (![A_182, B_183]: (r2_hidden('#skF_2'(A_182, B_183), k3_xboole_0(A_182, B_183)) | r1_xboole_0(A_182, B_183))), inference(cnfTransformation, [status(thm)], [f_59])).
% 30.24/22.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 30.24/22.16  tff(c_610, plain, (![A_1, B_2, C_150]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_150, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_596])).
% 30.24/22.16  tff(c_849, plain, (![B_183, A_182]: (~r1_xboole_0(B_183, A_182) | r1_xboole_0(A_182, B_183))), inference(resolution, [status(thm)], [c_830, c_610])).
% 30.24/22.16  tff(c_110600, plain, (r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_110548, c_849])).
% 30.24/22.16  tff(c_110639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_528, c_110600])).
% 30.24/22.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.24/22.16  
% 30.24/22.16  Inference rules
% 30.24/22.16  ----------------------
% 30.24/22.16  #Ref     : 0
% 30.24/22.16  #Sup     : 29432
% 30.24/22.16  #Fact    : 0
% 30.24/22.16  #Define  : 0
% 30.24/22.16  #Split   : 4
% 30.24/22.16  #Chain   : 0
% 30.24/22.16  #Close   : 0
% 30.24/22.16  
% 30.24/22.16  Ordering : KBO
% 30.24/22.16  
% 30.24/22.16  Simplification rules
% 30.24/22.16  ----------------------
% 30.24/22.16  #Subsume      : 11399
% 30.24/22.16  #Demod        : 25090
% 30.24/22.16  #Tautology    : 9833
% 30.24/22.16  #SimpNegUnit  : 505
% 30.24/22.16  #BackRed      : 0
% 30.24/22.16  
% 30.24/22.16  #Partial instantiations: 0
% 30.24/22.16  #Strategies tried      : 1
% 30.24/22.16  
% 30.24/22.16  Timing (in seconds)
% 30.24/22.16  ----------------------
% 30.24/22.16  Preprocessing        : 0.32
% 30.24/22.16  Parsing              : 0.17
% 30.24/22.16  CNF conversion       : 0.03
% 30.24/22.16  Main loop            : 20.98
% 30.24/22.16  Inferencing          : 2.19
% 30.24/22.16  Reduction            : 3.95
% 30.24/22.16  Demodulation         : 3.06
% 30.24/22.16  BG Simplification    : 0.23
% 30.24/22.16  Subsumption          : 13.95
% 30.24/22.16  Abstraction          : 0.42
% 30.24/22.16  MUC search           : 0.00
% 30.24/22.16  Cooper               : 0.00
% 30.24/22.16  Total                : 21.33
% 30.24/22.16  Index Insertion      : 0.00
% 30.24/22.16  Index Deletion       : 0.00
% 30.24/22.16  Index Matching       : 0.00
% 30.24/22.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
