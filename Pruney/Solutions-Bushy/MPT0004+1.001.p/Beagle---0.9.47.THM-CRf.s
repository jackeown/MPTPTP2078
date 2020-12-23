%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:33 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 101 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 154 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_35,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
        & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_21,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_25,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_21])).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_10])).

tff(c_43,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k3_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_47,plain,(
    k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_14,plain,(
    ! [C_10] :
      ( r1_xboole_0('#skF_2','#skF_3')
      | ~ r2_hidden(C_10,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    ! [C_19] : ~ r2_hidden(C_19,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_59,plain,(
    v1_xboole_0(k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_12])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_62])).

tff(c_67,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_6])).

tff(c_16,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3'))
      | ~ r2_hidden(C_10,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_4',k1_xboole_0)
      | ~ r2_hidden(C_10,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_16])).

tff(c_78,plain,(
    ! [C_20] : ~ r2_hidden(C_20,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_83,plain,(
    v1_xboole_0(k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_86,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_12])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_86])).

tff(c_91,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_94,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_94])).

tff(c_99,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_102,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_102])).

tff(c_100,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_20])).

tff(c_120,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_125,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_120])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_125])).

%------------------------------------------------------------------------------
