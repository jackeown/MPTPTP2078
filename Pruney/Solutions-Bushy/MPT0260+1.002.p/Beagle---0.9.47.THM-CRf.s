%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0260+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:00 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  59 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  86 expanded)
%              Number of equality atoms :    9 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [D_10,B_6] : r2_hidden(D_10,k2_tarski(D_10,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    r1_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_156,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_164,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_156])).

tff(c_238,plain,(
    ! [D_49,A_50,B_51] :
      ( r2_hidden(D_49,k3_xboole_0(A_50,B_51))
      | ~ r2_hidden(D_49,B_51)
      | ~ r2_hidden(D_49,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_312,plain,(
    ! [D_55] :
      ( r2_hidden(D_55,k1_xboole_0)
      | ~ r2_hidden(D_55,'#skF_7')
      | ~ r2_hidden(D_55,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_238])).

tff(c_320,plain,
    ( r2_hidden('#skF_5',k1_xboole_0)
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_312])).

tff(c_324,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_320])).

tff(c_46,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_188,plain,(
    ! [D_38,A_39,B_40] :
      ( r2_hidden(D_38,A_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_206,plain,(
    ! [D_38,A_19] :
      ( r2_hidden(D_38,A_19)
      | ~ r2_hidden(D_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_188])).

tff(c_329,plain,(
    ! [A_19] : r2_hidden('#skF_5',A_19) ),
    inference(resolution,[status(thm)],[c_324,c_206])).

tff(c_333,plain,(
    ! [A_56] : r2_hidden('#skF_5',A_56) ),
    inference(resolution,[status(thm)],[c_324,c_206])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_372,plain,(
    ! [A_60] : ~ r2_hidden(A_60,'#skF_5') ),
    inference(resolution,[status(thm)],[c_333,c_2])).

tff(c_377,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_329,c_372])).

%------------------------------------------------------------------------------
