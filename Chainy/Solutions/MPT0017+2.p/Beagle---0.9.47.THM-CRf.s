%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0017+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :   62 (  70 expanded)
%              Number of leaves         :   42 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  47 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_259,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_290,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

tff(f_308,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_275,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_204,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_394,plain,(
    ! [B_135,A_136] : k2_xboole_0(B_135,A_136) = k2_xboole_0(A_136,B_135) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_224,plain,(
    ! [A_104,B_105] : r1_tarski(A_104,k2_xboole_0(A_104,B_105)) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_415,plain,(
    ! [A_136,B_135] : r1_tarski(A_136,k2_xboole_0(B_135,A_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_224])).

tff(c_104,plain,(
    ! [A_44] : k2_xboole_0(A_44,A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1899,plain,(
    ! [A_272,C_273,B_274] :
      ( r1_tarski(k2_xboole_0(A_272,C_273),k2_xboole_0(B_274,C_273))
      | ~ r1_tarski(A_272,B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_3528,plain,(
    ! [A_359,A_360] :
      ( r1_tarski(k2_xboole_0(A_359,A_360),A_360)
      | ~ r1_tarski(A_359,A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_1899])).

tff(c_192,plain,(
    ! [B_82,A_81] :
      ( B_82 = A_81
      | ~ r1_tarski(B_82,A_81)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_3555,plain,(
    ! [A_359,A_360] :
      ( k2_xboole_0(A_359,A_360) = A_360
      | ~ r1_tarski(A_360,k2_xboole_0(A_359,A_360))
      | ~ r1_tarski(A_359,A_360) ) ),
    inference(resolution,[status(thm)],[c_3528,c_192])).

tff(c_3611,plain,(
    ! [A_361,A_362] :
      ( k2_xboole_0(A_361,A_362) = A_362
      | ~ r1_tarski(A_361,A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_3555])).

tff(c_3682,plain,(
    k2_xboole_0('#skF_19','#skF_20') = '#skF_20' ),
    inference(resolution,[status(thm)],[c_204,c_3611])).

tff(c_214,plain,(
    ! [A_93,B_94,C_95] : k2_xboole_0(k2_xboole_0(A_93,B_94),C_95) = k2_xboole_0(A_93,k2_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1695,plain,(
    ! [A_262,B_263,C_264] : k2_xboole_0(k2_xboole_0(A_262,B_263),C_264) = k2_xboole_0(A_262,k2_xboole_0(B_263,C_264)) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_2045,plain,(
    ! [C_282,A_283,B_284] : r1_tarski(C_282,k2_xboole_0(A_283,k2_xboole_0(B_284,C_282))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_415])).

tff(c_2084,plain,(
    ! [C_282,B_284,A_5] : r1_tarski(C_282,k2_xboole_0(k2_xboole_0(B_284,C_282),A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2045])).

tff(c_2111,plain,(
    ! [C_282,B_284,A_5] : r1_tarski(C_282,k2_xboole_0(B_284,k2_xboole_0(C_282,A_5))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2084])).

tff(c_3725,plain,(
    ! [B_284] : r1_tarski('#skF_19',k2_xboole_0(B_284,'#skF_20')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3682,c_2111])).

tff(c_202,plain,(
    ~ r1_tarski('#skF_19',k2_xboole_0('#skF_21','#skF_20')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_3804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3725,c_202])).
%------------------------------------------------------------------------------
