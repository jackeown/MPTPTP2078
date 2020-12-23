%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0400+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:15 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   32 (  40 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_setfam_1(A,B)
          & r1_setfam_1(B,C) )
       => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_16,plain,(
    r1_setfam_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    r1_setfam_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1,B_2,C_11] :
      ( r2_hidden('#skF_2'(A_1,B_2,C_11),B_2)
      | ~ r2_hidden(C_11,A_1)
      | ~ r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [C_11,A_1,B_2] :
      ( r1_tarski(C_11,'#skF_2'(A_1,B_2,C_11))
      | ~ r2_hidden(C_11,A_1)
      | ~ r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    ! [C_24,A_25,B_26] :
      ( r1_tarski(C_24,'#skF_2'(A_25,B_26,C_24))
      | ~ r2_hidden(C_24,A_25)
      | ~ r1_setfam_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_30,A_31,B_32,C_33] :
      ( r1_tarski(A_30,'#skF_2'(A_31,B_32,C_33))
      | ~ r1_tarski(A_30,C_33)
      | ~ r2_hidden(C_33,A_31)
      | ~ r1_setfam_1(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_10])).

tff(c_6,plain,(
    ! [A_1,B_2,D_10] :
      ( ~ r1_tarski('#skF_1'(A_1,B_2),D_10)
      | ~ r2_hidden(D_10,B_2)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,(
    ! [A_50,B_49,A_47,C_48,B_46] :
      ( ~ r2_hidden('#skF_2'(A_47,B_46,C_48),B_49)
      | r1_setfam_1(A_50,B_49)
      | ~ r1_tarski('#skF_1'(A_50,B_49),C_48)
      | ~ r2_hidden(C_48,A_47)
      | ~ r1_setfam_1(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_30,c_6])).

tff(c_61,plain,(
    ! [A_51,B_52,C_53,A_54] :
      ( r1_setfam_1(A_51,B_52)
      | ~ r1_tarski('#skF_1'(A_51,B_52),C_53)
      | ~ r2_hidden(C_53,A_54)
      | ~ r1_setfam_1(A_54,B_52) ) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_70,plain,(
    ! [A_57,B_56,A_59,B_58,A_55] :
      ( r1_setfam_1(A_55,B_56)
      | ~ r2_hidden('#skF_2'(A_59,B_58,'#skF_1'(A_55,B_56)),A_57)
      | ~ r1_setfam_1(A_57,B_56)
      | ~ r2_hidden('#skF_1'(A_55,B_56),A_59)
      | ~ r1_setfam_1(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_85,plain,(
    ! [A_66,B_67,B_68,A_69] :
      ( r1_setfam_1(A_66,B_67)
      | ~ r1_setfam_1(B_68,B_67)
      | ~ r2_hidden('#skF_1'(A_66,B_67),A_69)
      | ~ r1_setfam_1(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_92,plain,(
    ! [A_70,A_71] :
      ( r1_setfam_1(A_70,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_70,'#skF_5'),A_71)
      | ~ r1_setfam_1(A_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_98,plain,(
    ! [A_72] :
      ( ~ r1_setfam_1(A_72,'#skF_4')
      | r1_setfam_1(A_72,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_12,plain,(
    ~ r1_setfam_1('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ~ r1_setfam_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_103])).

%------------------------------------------------------------------------------
