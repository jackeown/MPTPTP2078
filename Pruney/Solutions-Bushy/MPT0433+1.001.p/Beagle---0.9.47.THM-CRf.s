%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0433+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:18 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :   48 (  88 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 171 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_6 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_180,plain,(
    ! [A_61,B_62,B_63] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_61,B_62),B_63),B_62)
      | r1_tarski(k3_xboole_0(A_61,B_62),B_63) ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_203,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),B_62) ),
    inference(resolution,[status(thm)],[c_180,c_6])).

tff(c_162,plain,(
    ! [C_59,A_60] :
      ( r2_hidden(k4_tarski(C_59,'#skF_5'(A_60,k1_relat_1(A_60),C_59)),A_60)
      | ~ r2_hidden(C_59,k1_relat_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_996,plain,(
    ! [C_175,A_176,B_177] :
      ( r2_hidden(k4_tarski(C_175,'#skF_5'(A_176,k1_relat_1(A_176),C_175)),B_177)
      | ~ r1_tarski(A_176,B_177)
      | ~ r2_hidden(C_175,k1_relat_1(A_176)) ) ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_12,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1020,plain,(
    ! [C_178,B_179,A_180] :
      ( r2_hidden(C_178,k1_relat_1(B_179))
      | ~ r1_tarski(A_180,B_179)
      | ~ r2_hidden(C_178,k1_relat_1(A_180)) ) ),
    inference(resolution,[status(thm)],[c_996,c_12])).

tff(c_1036,plain,(
    ! [C_181,B_182,A_183] :
      ( r2_hidden(C_181,k1_relat_1(B_182))
      | ~ r2_hidden(C_181,k1_relat_1(k3_xboole_0(A_183,B_182))) ) ),
    inference(resolution,[status(thm)],[c_203,c_1020])).

tff(c_1516,plain,(
    ! [A_199,B_200,B_201] :
      ( r2_hidden('#skF_1'(k1_relat_1(k3_xboole_0(A_199,B_200)),B_201),k1_relat_1(B_200))
      | r1_tarski(k1_relat_1(k3_xboole_0(A_199,B_200)),B_201) ) ),
    inference(resolution,[status(thm)],[c_8,c_1036])).

tff(c_1553,plain,(
    ! [A_202,B_203] : r1_tarski(k1_relat_1(k3_xboole_0(A_202,B_203)),k1_relat_1(B_203)) ),
    inference(resolution,[status(thm)],[c_1516,c_6])).

tff(c_1563,plain,(
    ! [B_2,A_1] : r1_tarski(k1_relat_1(k3_xboole_0(B_2,A_1)),k1_relat_1(B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1553])).

tff(c_1551,plain,(
    ! [A_199,B_200] : r1_tarski(k1_relat_1(k3_xboole_0(A_199,B_200)),k1_relat_1(B_200)) ),
    inference(resolution,[status(thm)],[c_1516,c_6])).

tff(c_111,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_3,B_4,B_51] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_51)
      | ~ r1_tarski(A_3,B_51)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_115,plain,(
    ! [D_53,A_54,B_55] :
      ( r2_hidden(D_53,k3_xboole_0(A_54,B_55))
      | ~ r2_hidden(D_53,B_55)
      | ~ r2_hidden(D_53,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4745,plain,(
    ! [A_332,A_333,B_334] :
      ( r1_tarski(A_332,k3_xboole_0(A_333,B_334))
      | ~ r2_hidden('#skF_1'(A_332,k3_xboole_0(A_333,B_334)),B_334)
      | ~ r2_hidden('#skF_1'(A_332,k3_xboole_0(A_333,B_334)),A_333) ) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_12631,plain,(
    ! [A_571,A_572,B_573] :
      ( ~ r2_hidden('#skF_1'(A_571,k3_xboole_0(A_572,B_573)),A_572)
      | ~ r1_tarski(A_571,B_573)
      | r1_tarski(A_571,k3_xboole_0(A_572,B_573)) ) ),
    inference(resolution,[status(thm)],[c_114,c_4745])).

tff(c_12782,plain,(
    ! [A_574,B_575,B_576] :
      ( ~ r1_tarski(A_574,B_575)
      | ~ r1_tarski(A_574,B_576)
      | r1_tarski(A_574,k3_xboole_0(B_576,B_575)) ) ),
    inference(resolution,[status(thm)],[c_114,c_12631])).

tff(c_40,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_8','#skF_9')),k3_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12816,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_8','#skF_9')),k1_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_8','#skF_9')),k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_12782,c_40])).

tff(c_12842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_1551,c_12816])).

%------------------------------------------------------------------------------
