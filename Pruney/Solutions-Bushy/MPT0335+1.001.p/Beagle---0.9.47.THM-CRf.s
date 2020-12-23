%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0335+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:07 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  87 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_41,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_48,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_105,plain,(
    ! [D_33,B_34,A_35] :
      ( r2_hidden(D_33,B_34)
      | ~ r2_hidden(D_33,k3_xboole_0(A_35,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [D_36] :
      ( r2_hidden(D_36,'#skF_7')
      | ~ r2_hidden(D_36,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_105])).

tff(c_114,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_46,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_130,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(k3_xboole_0(A_39,C_40),k3_xboole_0(B_41,C_40))
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_158,plain,(
    ! [A_46] :
      ( r1_tarski(k3_xboole_0(A_46,'#skF_7'),k1_tarski('#skF_8'))
      | ~ r1_tarski(A_46,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_130])).

tff(c_34,plain,(
    ! [B_13,A_12] :
      ( k1_tarski(B_13) = A_12
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_tarski(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_319,plain,(
    ! [A_63] :
      ( k3_xboole_0(A_63,'#skF_7') = k1_tarski('#skF_8')
      | k3_xboole_0(A_63,'#skF_7') = k1_xboole_0
      | ~ r1_tarski(A_63,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_158,c_34])).

tff(c_322,plain,
    ( k3_xboole_0('#skF_5','#skF_7') = k1_tarski('#skF_8')
    | k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_319])).

tff(c_325,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_322])).

tff(c_137,plain,(
    ! [D_42,A_43,B_44] :
      ( r2_hidden(D_42,k3_xboole_0(A_43,B_44))
      | ~ r2_hidden(D_42,B_44)
      | ~ r2_hidden(D_42,A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    ! [B_19,A_18] :
      ( ~ v1_xboole_0(B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_152,plain,(
    ! [A_43,B_44,D_42] :
      ( ~ v1_xboole_0(k3_xboole_0(A_43,B_44))
      | ~ r2_hidden(D_42,B_44)
      | ~ r2_hidden(D_42,A_43) ) ),
    inference(resolution,[status(thm)],[c_137,c_44])).

tff(c_370,plain,(
    ! [D_42] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_42,'#skF_7')
      | ~ r2_hidden(D_42,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_152])).

tff(c_425,plain,(
    ! [D_68] :
      ( ~ r2_hidden(D_68,'#skF_7')
      | ~ r2_hidden(D_68,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_370])).

tff(c_436,plain,(
    ~ r2_hidden('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_425])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_436])).

%------------------------------------------------------------------------------
