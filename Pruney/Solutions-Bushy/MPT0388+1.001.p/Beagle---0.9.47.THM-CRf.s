%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:13 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 103 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_tarski(B,C) )
       => ( A = k1_xboole_0
          | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_5'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden('#skF_5'(A_30,B_31),B_31)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ! [A_20] : r1_tarski(A_20,A_20) ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [A_47,C_48] :
      ( r2_hidden('#skF_1'(A_47,k1_setfam_1(A_47),C_48),A_47)
      | r2_hidden(C_48,k1_setfam_1(A_47))
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [C_26] :
      ( r1_tarski('#skF_7',C_26)
      | ~ r2_hidden(C_26,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    ! [C_48] :
      ( r1_tarski('#skF_7','#skF_1'('#skF_6',k1_setfam_1('#skF_6'),C_48))
      | r2_hidden(C_48,k1_setfam_1('#skF_6'))
      | k1_xboole_0 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_92,c_34])).

tff(c_108,plain,(
    ! [C_48] :
      ( r1_tarski('#skF_7','#skF_1'('#skF_6',k1_setfam_1('#skF_6'),C_48))
      | r2_hidden(C_48,k1_setfam_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_100])).

tff(c_55,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [A_40,B_41,B_42] :
      ( r2_hidden('#skF_5'(A_40,B_41),B_42)
      | ~ r1_tarski(A_40,B_42)
      | r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_24,plain,(
    ! [C_24,B_21,A_20] :
      ( r2_hidden(C_24,B_21)
      | ~ r2_hidden(C_24,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_144,plain,(
    ! [A_55,B_56,B_57,B_58] :
      ( r2_hidden('#skF_5'(A_55,B_56),B_57)
      | ~ r1_tarski(B_58,B_57)
      | ~ r1_tarski(A_55,B_58)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_63,c_24])).

tff(c_657,plain,(
    ! [A_137,B_138,C_139] :
      ( r2_hidden('#skF_5'(A_137,B_138),'#skF_1'('#skF_6',k1_setfam_1('#skF_6'),C_139))
      | ~ r1_tarski(A_137,'#skF_7')
      | r1_tarski(A_137,B_138)
      | r2_hidden(C_139,k1_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_144])).

tff(c_16,plain,(
    ! [C_13,A_1] :
      ( ~ r2_hidden(C_13,'#skF_1'(A_1,k1_setfam_1(A_1),C_13))
      | r2_hidden(C_13,k1_setfam_1(A_1))
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_661,plain,(
    ! [A_137,B_138] :
      ( k1_xboole_0 = '#skF_6'
      | ~ r1_tarski(A_137,'#skF_7')
      | r1_tarski(A_137,B_138)
      | r2_hidden('#skF_5'(A_137,B_138),k1_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_657,c_16])).

tff(c_676,plain,(
    ! [A_140,B_141] :
      ( ~ r1_tarski(A_140,'#skF_7')
      | r1_tarski(A_140,B_141)
      | r2_hidden('#skF_5'(A_140,B_141),k1_setfam_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_661])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_5'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_700,plain,(
    ! [A_142] :
      ( ~ r1_tarski(A_142,'#skF_7')
      | r1_tarski(A_142,k1_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_676,c_26])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_7',k1_setfam_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_709,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_700,c_30])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_709])).

%------------------------------------------------------------------------------
