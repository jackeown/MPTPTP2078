%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0567+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:30 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   34 (  47 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  58 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_38,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_26,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_33,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_29])).

tff(c_34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_20])).

tff(c_117,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_2'(A_77,B_78,C_79),B_78)
      | r2_hidden('#skF_3'(A_77,B_78,C_79),C_79)
      | k10_relat_1(A_77,B_78) = C_79
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_45,A_44] :
      ( ~ v1_xboole_0(B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_182,plain,(
    ! [B_80,A_81,C_82] :
      ( ~ v1_xboole_0(B_80)
      | r2_hidden('#skF_3'(A_81,B_80,C_82),C_82)
      | k10_relat_1(A_81,B_80) = C_82
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_117,c_24])).

tff(c_215,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ v1_xboole_0(C_83)
      | ~ v1_xboole_0(B_84)
      | k10_relat_1(A_85,B_84) = C_83
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_182,c_24])).

tff(c_219,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | k10_relat_1(A_87,B_86) = k1_xboole_0
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_34,c_215])).

tff(c_224,plain,(
    ! [A_91] :
      ( k10_relat_1(A_91,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_34,c_219])).

tff(c_227,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_224])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_227])).

%------------------------------------------------------------------------------
