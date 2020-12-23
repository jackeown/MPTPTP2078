%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0538+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:27 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  47 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_3 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_47,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [A_27] :
      ( v1_relat_1(A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_31])).

tff(c_12,plain,(
    ! [A_2,B_3,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_2,B_3,C_13),'#skF_2'(A_2,B_3,C_13)),B_3)
      | r2_hidden(k4_tarski('#skF_3'(A_2,B_3,C_13),'#skF_4'(A_2,B_3,C_13)),C_13)
      | k8_relat_1(A_2,B_3) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_300,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_81,B_82,C_83),'#skF_2'(A_81,B_82,C_83)),C_83)
      | r2_hidden(k4_tarski('#skF_3'(A_81,B_82,C_83),'#skF_4'(A_81,B_82,C_83)),C_83)
      | k8_relat_1(A_81,B_82) = C_83
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_311,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_3'(A_84,B_85,B_85),'#skF_4'(A_84,B_85,B_85)),B_85)
      | k8_relat_1(A_84,B_85) = B_85
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_300])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( ~ v1_xboole_0(B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_340,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | k8_relat_1(A_87,B_86) = B_86
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_311,c_28])).

tff(c_342,plain,(
    ! [A_87] :
      ( k8_relat_1(A_87,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_340])).

tff(c_345,plain,(
    ! [A_87] : k8_relat_1(A_87,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_342])).

tff(c_30,plain,(
    k8_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_30])).

%------------------------------------------------------------------------------
