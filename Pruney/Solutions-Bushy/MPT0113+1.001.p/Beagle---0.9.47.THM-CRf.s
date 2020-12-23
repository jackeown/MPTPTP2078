%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0113+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:44 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :   54 (  78 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 160 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    r1_tarski('#skF_5',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_42,A_43,B_44] :
      ( r1_tarski(A_42,A_43)
      | ~ r1_tarski(A_42,k4_xboole_0(A_43,B_44)) ) ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_104,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_93])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_104])).

tff(c_112,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_4'(A_17,B_18),A_17)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_4'(A_17,B_18),B_18)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_167,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(A_66,C_67)
      | ~ r1_tarski(B_68,C_67)
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,k4_xboole_0('#skF_6','#skF_7'))
      | ~ r1_tarski(A_66,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_167])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ! [A_1,B_2,B_64] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_64)
      | ~ r1_tarski(A_1,B_64)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_140,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1441,plain,(
    ! [A_269,B_270,B_271] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_269,B_270),B_271),B_270)
      | r1_tarski(k4_xboole_0(A_269,B_270),B_271) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_1452,plain,(
    ! [A_272,B_273,B_274] :
      ( ~ r1_tarski(k4_xboole_0(A_272,B_273),B_273)
      | r1_tarski(k4_xboole_0(A_272,B_273),B_274) ) ),
    inference(resolution,[status(thm)],[c_164,c_1441])).

tff(c_1661,plain,(
    ! [A_278,B_279] :
      ( r1_tarski(k4_xboole_0(A_278,k4_xboole_0('#skF_6','#skF_7')),B_279)
      | ~ r1_tarski(k4_xboole_0(A_278,k4_xboole_0('#skF_6','#skF_7')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_179,c_1452])).

tff(c_1682,plain,(
    ! [B_279] : r1_tarski(k4_xboole_0('#skF_5',k4_xboole_0('#skF_6','#skF_7')),B_279) ),
    inference(resolution,[status(thm)],[c_28,c_1661])).

tff(c_180,plain,(
    ! [D_69,A_70,B_71] :
      ( r2_hidden(D_69,k4_xboole_0(A_70,B_71))
      | r2_hidden(D_69,B_71)
      | ~ r2_hidden(D_69,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3100,plain,(
    ! [D_355,B_356,A_357,B_358] :
      ( r2_hidden(D_355,B_356)
      | ~ r1_tarski(k4_xboole_0(A_357,B_358),B_356)
      | r2_hidden(D_355,B_358)
      | ~ r2_hidden(D_355,A_357) ) ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_3175,plain,(
    ! [D_355,B_279] :
      ( r2_hidden(D_355,B_279)
      | r2_hidden(D_355,k4_xboole_0('#skF_6','#skF_7'))
      | ~ r2_hidden(D_355,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1682,c_3100])).

tff(c_6891,plain,(
    ! [D_518] :
      ( ~ r2_hidden(D_518,'#skF_5')
      | r2_hidden(D_518,k4_xboole_0('#skF_6','#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3175])).

tff(c_2100,plain,(
    ! [A_300,A_301,B_302] :
      ( ~ r2_hidden('#skF_4'(A_300,k4_xboole_0(A_301,B_302)),B_302)
      | r1_xboole_0(A_300,k4_xboole_0(A_301,B_302)) ) ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_2127,plain,(
    ! [A_303,A_304] : r1_xboole_0(A_303,k4_xboole_0(A_304,A_303)) ),
    inference(resolution,[status(thm)],[c_34,c_2100])).

tff(c_30,plain,(
    ! [A_17,B_18,C_21] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r2_hidden(C_21,B_18)
      | ~ r2_hidden(C_21,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2130,plain,(
    ! [C_21,A_304,A_303] :
      ( ~ r2_hidden(C_21,k4_xboole_0(A_304,A_303))
      | ~ r2_hidden(C_21,A_303) ) ),
    inference(resolution,[status(thm)],[c_2127,c_30])).

tff(c_6967,plain,(
    ! [D_519] :
      ( ~ r2_hidden(D_519,'#skF_7')
      | ~ r2_hidden(D_519,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6891,c_2130])).

tff(c_7693,plain,(
    ! [A_537] :
      ( ~ r2_hidden('#skF_4'(A_537,'#skF_7'),'#skF_5')
      | r1_xboole_0(A_537,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_6967])).

tff(c_7713,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_7693])).

tff(c_7720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_112,c_7713])).

%------------------------------------------------------------------------------
