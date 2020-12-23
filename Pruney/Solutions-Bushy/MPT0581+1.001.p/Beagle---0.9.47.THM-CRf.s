%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0581+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:32 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  46 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C,D] :
                ( ( k7_relat_1(A,C) = k7_relat_1(B,C)
                  & k7_relat_1(A,D) = k7_relat_1(B,D) )
               => k7_relat_1(A,k2_xboole_0(C,D)) = k7_relat_1(B,k2_xboole_0(C,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_relat_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_relat_1)).

tff(c_4,plain,(
    k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    k7_relat_1('#skF_2','#skF_3') = k7_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_21,plain,(
    ! [C_11,A_12,B_13] :
      ( k2_xboole_0(k7_relat_1(C_11,A_12),k7_relat_1(C_11,B_13)) = k7_relat_1(C_11,k2_xboole_0(A_12,B_13))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_39,plain,(
    ! [A_12] :
      ( k2_xboole_0(k7_relat_1('#skF_2',A_12),k7_relat_1('#skF_1','#skF_4')) = k7_relat_1('#skF_2',k2_xboole_0(A_12,'#skF_4'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21])).

tff(c_65,plain,(
    ! [A_15] : k2_xboole_0(k7_relat_1('#skF_2',A_15),k7_relat_1('#skF_1','#skF_4')) = k7_relat_1('#skF_2',k2_xboole_0(A_15,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_39])).

tff(c_74,plain,(
    k2_xboole_0(k7_relat_1('#skF_1','#skF_3'),k7_relat_1('#skF_1','#skF_4')) = k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( k2_xboole_0(k7_relat_1(C_3,A_1),k7_relat_1(C_3,B_2)) = k7_relat_1(C_3,k2_xboole_0(A_1,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_156,plain,
    ( k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_163,plain,(
    k7_relat_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_156])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_163])).

%------------------------------------------------------------------------------
