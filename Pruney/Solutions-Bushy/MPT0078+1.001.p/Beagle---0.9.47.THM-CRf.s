%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0078+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:41 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 126 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 267 expanded)
%              Number of equality atoms :   13 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k2_xboole_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    ! [D_37,A_38,B_39] :
      ( ~ r2_hidden(D_37,A_38)
      | r2_hidden(D_37,k2_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [D_37] :
      ( ~ r2_hidden(D_37,'#skF_6')
      | r2_hidden(D_37,k2_xboole_0('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_108])).

tff(c_330,plain,(
    ! [D_65,B_66,A_67] :
      ( r2_hidden(D_65,B_66)
      | r2_hidden(D_65,A_67)
      | ~ r2_hidden(D_65,k2_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_351,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,'#skF_7')
      | r2_hidden(D_68,'#skF_8')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_115,c_330])).

tff(c_58,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_68])).

tff(c_227,plain,(
    ! [D_57,A_58,B_59] :
      ( r2_hidden(D_57,k3_xboole_0(A_58,B_59))
      | ~ r2_hidden(D_57,B_59)
      | ~ r2_hidden(D_57,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [D_60] :
      ( r2_hidden(D_60,k1_xboole_0)
      | ~ r2_hidden(D_60,'#skF_7')
      | ~ r2_hidden(D_60,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_227])).

tff(c_56,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_79,plain,(
    k3_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_68])).

tff(c_90,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,A_30)
      | ~ r2_hidden(D_29,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [D_29] :
      ( r2_hidden(D_29,'#skF_8')
      | ~ r2_hidden(D_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_90])).

tff(c_268,plain,(
    ! [D_60] :
      ( r2_hidden(D_60,'#skF_8')
      | ~ r2_hidden(D_60,'#skF_7')
      | ~ r2_hidden(D_60,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_250,c_96])).

tff(c_368,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,'#skF_8')
      | ~ r2_hidden(D_69,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_351,c_268])).

tff(c_378,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_1'('#skF_6',B_70),'#skF_8')
      | r1_tarski('#skF_6',B_70) ) ),
    inference(resolution,[status(thm)],[c_12,c_368])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_386,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_378,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_408,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_386,c_2])).

tff(c_411,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_408])).

tff(c_18,plain,(
    ! [D_13,A_8,B_9] :
      ( ~ r2_hidden(D_13,A_8)
      | r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_387,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,'#skF_7')
      | r2_hidden(D_71,'#skF_6')
      | ~ r2_hidden(D_71,k2_xboole_0('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_330])).

tff(c_412,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,'#skF_7')
      | r2_hidden(D_72,'#skF_6')
      | ~ r2_hidden(D_72,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18,c_387])).

tff(c_271,plain,(
    ! [D_61] :
      ( r2_hidden(D_61,k1_xboole_0)
      | ~ r2_hidden(D_61,'#skF_7')
      | ~ r2_hidden(D_61,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_227])).

tff(c_93,plain,(
    ! [D_29] :
      ( r2_hidden(D_29,'#skF_6')
      | ~ r2_hidden(D_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_90])).

tff(c_290,plain,(
    ! [D_61] :
      ( r2_hidden(D_61,'#skF_6')
      | ~ r2_hidden(D_61,'#skF_7')
      | ~ r2_hidden(D_61,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_271,c_93])).

tff(c_425,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,'#skF_6')
      | ~ r2_hidden(D_73,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_412,c_290])).

tff(c_442,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_74,'#skF_6'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_425,c_10])).

tff(c_454,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_442])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_411,c_454])).

%------------------------------------------------------------------------------
