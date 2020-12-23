%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0093+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:43 EST 2020

% Result     : Theorem 23.13s
% Output     : CNFRefutation 23.24s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 114 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(c_50,plain,(
    ~ r1_tarski('#skF_6',k4_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_96,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_44] : r1_tarski(A_44,A_44) ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_54,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_267,plain,(
    ! [A_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_74,B_75),B_76)
      | ~ r1_tarski(A_74,B_76)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72860,plain,(
    ! [A_1415,B_1416,B_1417,B_1418] :
      ( r2_hidden('#skF_1'(A_1415,B_1416),B_1417)
      | ~ r1_tarski(B_1418,B_1417)
      | ~ r1_tarski(A_1415,B_1418)
      | r1_tarski(A_1415,B_1416) ) ),
    inference(resolution,[status(thm)],[c_267,c_2])).

tff(c_72948,plain,(
    ! [A_1419,B_1420] :
      ( r2_hidden('#skF_1'(A_1419,B_1420),'#skF_7')
      | ~ r1_tarski(A_1419,'#skF_6')
      | r1_tarski(A_1419,B_1420) ) ),
    inference(resolution,[status(thm)],[c_54,c_72860])).

tff(c_149,plain,(
    ! [D_53,A_54,B_55] :
      ( r2_hidden(D_53,k4_xboole_0(A_54,B_55))
      | r2_hidden(D_53,B_55)
      | ~ r2_hidden(D_53,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_169,plain,(
    ! [A_1,A_54,B_55] :
      ( r1_tarski(A_1,k4_xboole_0(A_54,B_55))
      | r2_hidden('#skF_1'(A_1,k4_xboole_0(A_54,B_55)),B_55)
      | ~ r2_hidden('#skF_1'(A_1,k4_xboole_0(A_54,B_55)),A_54) ) ),
    inference(resolution,[status(thm)],[c_149,c_4])).

tff(c_76002,plain,(
    ! [A_1446,B_1447] :
      ( r2_hidden('#skF_1'(A_1446,k4_xboole_0('#skF_7',B_1447)),B_1447)
      | ~ r1_tarski(A_1446,'#skF_6')
      | r1_tarski(A_1446,k4_xboole_0('#skF_7',B_1447)) ) ),
    inference(resolution,[status(thm)],[c_72948,c_169])).

tff(c_52,plain,(
    r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_63,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    k3_xboole_0('#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_178,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,k3_xboole_0(A_60,B_61))
      | ~ r2_hidden(D_59,B_61)
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_216,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k1_xboole_0)
      | ~ r2_hidden(D_68,'#skF_8')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_178])).

tff(c_48,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [D_26,B_27,A_28] :
      ( ~ r2_hidden(D_26,B_27)
      | ~ r2_hidden(D_26,k4_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [D_26,A_20] :
      ( ~ r2_hidden(D_26,A_20)
      | ~ r2_hidden(D_26,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_76])).

tff(c_133,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_1'(A_44,B_45),k1_xboole_0)
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_96,c_79])).

tff(c_1683,plain,(
    ! [A_165,B_166] :
      ( r1_tarski(A_165,B_166)
      | ~ r2_hidden('#skF_1'(A_165,B_166),'#skF_8')
      | ~ r2_hidden('#skF_1'(A_165,B_166),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_216,c_133])).

tff(c_1708,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_2),'#skF_8')
      | r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1683])).

tff(c_76068,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | r1_tarski('#skF_6',k4_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_76002,c_1708])).

tff(c_76167,plain,(
    r1_tarski('#skF_6',k4_xboole_0('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_76068])).

tff(c_76169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_76167])).

%------------------------------------------------------------------------------
