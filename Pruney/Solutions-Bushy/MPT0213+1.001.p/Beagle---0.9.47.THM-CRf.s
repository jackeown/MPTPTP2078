%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0213+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:55 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  47 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_46,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_35,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_26,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_27])).

tff(c_32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_20])).

tff(c_146,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_2'(A_51,B_52),A_51)
      | r2_hidden('#skF_3'(A_51,B_52),B_52)
      | k3_tarski(A_51) = B_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( ~ v1_xboole_0(B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_239,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(A_55)
      | r2_hidden('#skF_3'(A_55,B_56),B_56)
      | k3_tarski(A_55) = B_56 ) ),
    inference(resolution,[status(thm)],[c_146,c_24])).

tff(c_282,plain,(
    ! [B_57,A_58] :
      ( ~ v1_xboole_0(B_57)
      | ~ v1_xboole_0(A_58)
      | k3_tarski(A_58) = B_57 ) ),
    inference(resolution,[status(thm)],[c_239,c_24])).

tff(c_286,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(A_59)
      | k3_tarski(A_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_282])).

tff(c_289,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_286])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_289])).

%------------------------------------------------------------------------------
