%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0401+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:15 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    r1_setfam_1('#skF_6',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_43,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_4'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(C_33,A_31)
      | ~ r1_setfam_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_43,A_44,C_45] :
      ( '#skF_4'(A_43,k1_tarski(A_44),C_45) = A_44
      | ~ r2_hidden(C_45,A_43)
      | ~ r1_setfam_1(A_43,k1_tarski(A_44)) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_99,plain,(
    ! [C_48] :
      ( '#skF_4'('#skF_6',k1_tarski('#skF_5'),C_48) = '#skF_5'
      | ~ r2_hidden(C_48,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_14,plain,(
    ! [C_16,A_6,B_7] :
      ( r1_tarski(C_16,'#skF_4'(A_6,B_7,C_16))
      | ~ r2_hidden(C_16,A_6)
      | ~ r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [C_48] :
      ( r1_tarski(C_48,'#skF_5')
      | ~ r2_hidden(C_48,'#skF_6')
      | ~ r1_setfam_1('#skF_6',k1_tarski('#skF_5'))
      | ~ r2_hidden(C_48,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_14])).

tff(c_118,plain,(
    ! [C_49] :
      ( r1_tarski(C_49,'#skF_5')
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_105])).

tff(c_137,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_137])).

%------------------------------------------------------------------------------
