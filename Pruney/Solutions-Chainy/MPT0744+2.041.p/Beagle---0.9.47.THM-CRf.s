%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:20 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 172 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  134 ( 355 expanded)
%              Number of equality atoms :   15 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_63,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_66,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4783,plain,(
    ! [A_426,B_427] :
      ( r2_hidden('#skF_1'(A_426,B_427),A_426)
      | r1_tarski(A_426,B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4795,plain,(
    ! [A_426] : r1_tarski(A_426,A_426) ),
    inference(resolution,[status(thm)],[c_4783,c_4])).

tff(c_5418,plain,(
    ! [A_490,B_491] :
      ( r1_ordinal1(A_490,B_491)
      | ~ r1_tarski(A_490,B_491)
      | ~ v3_ordinal1(B_491)
      | ~ v3_ordinal1(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5430,plain,(
    ! [A_426] :
      ( r1_ordinal1(A_426,A_426)
      | ~ v3_ordinal1(A_426) ) ),
    inference(resolution,[status(thm)],[c_4795,c_5418])).

tff(c_34,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_tarski(A_20)) = k1_ordinal1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_135,plain,(
    ! [D_52,B_53,A_54] :
      ( ~ r2_hidden(D_52,B_53)
      | r2_hidden(D_52,k2_xboole_0(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_764,plain,(
    ! [D_129,A_130] :
      ( ~ r2_hidden(D_129,k1_tarski(A_130))
      | r2_hidden(D_129,k1_ordinal1(A_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_135])).

tff(c_783,plain,(
    ! [C_18] : r2_hidden(C_18,k1_ordinal1(C_18)) ),
    inference(resolution,[status(thm)],[c_34,c_764])).

tff(c_68,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_76,plain,
    ( r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | r1_ordinal1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_97,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_58,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ r1_ordinal1(A_25,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_79,plain,(
    ! [A_38] :
      ( v1_ordinal1(A_38)
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_87,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_79])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r2_xboole_0(A_12,B_13)
      | B_13 = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_518,plain,(
    ! [A_95,B_96] :
      ( r2_hidden(A_95,B_96)
      | ~ r2_xboole_0(A_95,B_96)
      | ~ v3_ordinal1(B_96)
      | ~ v1_ordinal1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4204,plain,(
    ! [A_407,B_408] :
      ( r2_hidden(A_407,B_408)
      | ~ v3_ordinal1(B_408)
      | ~ v1_ordinal1(A_407)
      | B_408 = A_407
      | ~ r1_tarski(A_407,B_408) ) ),
    inference(resolution,[status(thm)],[c_26,c_518])).

tff(c_194,plain,(
    ! [D_65,A_66,B_67] :
      ( ~ r2_hidden(D_65,A_66)
      | r2_hidden(D_65,k2_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_211,plain,(
    ! [D_68,A_69] :
      ( ~ r2_hidden(D_68,A_69)
      | r2_hidden(D_68,k1_ordinal1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_194])).

tff(c_70,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_132,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_70])).

tff(c_227,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_211,c_132])).

tff(c_4574,plain,
    ( ~ v3_ordinal1('#skF_8')
    | ~ v1_ordinal1('#skF_7')
    | '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_4204,c_227])).

tff(c_4694,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_66,c_4574])).

tff(c_4702,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4694])).

tff(c_4705,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_4702])).

tff(c_4709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_97,c_4705])).

tff(c_4710,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4694])).

tff(c_4714,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4710,c_132])).

tff(c_4721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_4714])).

tff(c_4722,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4724,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_4726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4722,c_4724])).

tff(c_4727,plain,(
    ~ r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_86,plain,(
    v1_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_79])).

tff(c_5464,plain,(
    ! [D_496,B_497,A_498] :
      ( r2_hidden(D_496,B_497)
      | r2_hidden(D_496,A_498)
      | ~ r2_hidden(D_496,k2_xboole_0(A_498,B_497)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8058,plain,(
    ! [D_724,A_725] :
      ( r2_hidden(D_724,k1_tarski(A_725))
      | r2_hidden(D_724,A_725)
      | ~ r2_hidden(D_724,k1_ordinal1(A_725)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_5464])).

tff(c_32,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8483,plain,(
    ! [D_726,A_727] :
      ( D_726 = A_727
      | r2_hidden(D_726,A_727)
      | ~ r2_hidden(D_726,k1_ordinal1(A_727)) ) ),
    inference(resolution,[status(thm)],[c_8058,c_32])).

tff(c_8587,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_4722,c_8483])).

tff(c_8588,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_8587])).

tff(c_50,plain,(
    ! [B_24,A_21] :
      ( r1_tarski(B_24,A_21)
      | ~ r2_hidden(B_24,A_21)
      | ~ v1_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8593,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | ~ v1_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8588,c_50])).

tff(c_8600,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8593])).

tff(c_56,plain,(
    ! [A_25,B_26] :
      ( r1_ordinal1(A_25,B_26)
      | ~ r1_tarski(A_25,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8610,plain,
    ( r1_ordinal1('#skF_7','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_8600,c_56])).

tff(c_8613,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_8610])).

tff(c_8615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4727,c_8613])).

tff(c_8616,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8587])).

tff(c_8621,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8616,c_4727])).

tff(c_8636,plain,(
    ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5430,c_8621])).

tff(c_8640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.81/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/2.62  
% 7.81/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/2.63  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 7.81/2.63  
% 7.81/2.63  %Foreground sorts:
% 7.81/2.63  
% 7.81/2.63  
% 7.81/2.63  %Background operators:
% 7.81/2.63  
% 7.81/2.63  
% 7.81/2.63  %Foreground operators:
% 7.81/2.63  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 7.81/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.81/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.81/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.81/2.63  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 7.81/2.63  tff('#skF_7', type, '#skF_7': $i).
% 7.81/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.81/2.63  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 7.81/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.81/2.63  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 7.81/2.63  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 7.81/2.63  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 7.81/2.63  tff('#skF_8', type, '#skF_8': $i).
% 7.81/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.81/2.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.81/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.81/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.81/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.81/2.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.81/2.63  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.81/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.81/2.63  
% 7.81/2.64  tff(f_111, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 7.81/2.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.81/2.64  tff(f_78, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 7.81/2.64  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.81/2.64  tff(f_63, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 7.81/2.64  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 7.81/2.64  tff(f_61, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 7.81/2.64  tff(f_48, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 7.81/2.64  tff(f_87, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 7.81/2.64  tff(f_70, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 7.81/2.64  tff(c_66, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.81/2.64  tff(c_4783, plain, (![A_426, B_427]: (r2_hidden('#skF_1'(A_426, B_427), A_426) | r1_tarski(A_426, B_427))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.81/2.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.81/2.64  tff(c_4795, plain, (![A_426]: (r1_tarski(A_426, A_426))), inference(resolution, [status(thm)], [c_4783, c_4])).
% 7.81/2.64  tff(c_5418, plain, (![A_490, B_491]: (r1_ordinal1(A_490, B_491) | ~r1_tarski(A_490, B_491) | ~v3_ordinal1(B_491) | ~v3_ordinal1(A_490))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.81/2.64  tff(c_5430, plain, (![A_426]: (r1_ordinal1(A_426, A_426) | ~v3_ordinal1(A_426))), inference(resolution, [status(thm)], [c_4795, c_5418])).
% 7.81/2.64  tff(c_34, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.81/2.64  tff(c_48, plain, (![A_20]: (k2_xboole_0(A_20, k1_tarski(A_20))=k1_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.81/2.64  tff(c_135, plain, (![D_52, B_53, A_54]: (~r2_hidden(D_52, B_53) | r2_hidden(D_52, k2_xboole_0(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.81/2.64  tff(c_764, plain, (![D_129, A_130]: (~r2_hidden(D_129, k1_tarski(A_130)) | r2_hidden(D_129, k1_ordinal1(A_130)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_135])).
% 7.81/2.64  tff(c_783, plain, (![C_18]: (r2_hidden(C_18, k1_ordinal1(C_18)))), inference(resolution, [status(thm)], [c_34, c_764])).
% 7.81/2.64  tff(c_68, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.81/2.64  tff(c_76, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | r1_ordinal1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.81/2.64  tff(c_97, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_76])).
% 7.81/2.64  tff(c_58, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~r1_ordinal1(A_25, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.81/2.64  tff(c_79, plain, (![A_38]: (v1_ordinal1(A_38) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.81/2.64  tff(c_87, plain, (v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_79])).
% 7.81/2.64  tff(c_26, plain, (![A_12, B_13]: (r2_xboole_0(A_12, B_13) | B_13=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.81/2.64  tff(c_518, plain, (![A_95, B_96]: (r2_hidden(A_95, B_96) | ~r2_xboole_0(A_95, B_96) | ~v3_ordinal1(B_96) | ~v1_ordinal1(A_95))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.81/2.64  tff(c_4204, plain, (![A_407, B_408]: (r2_hidden(A_407, B_408) | ~v3_ordinal1(B_408) | ~v1_ordinal1(A_407) | B_408=A_407 | ~r1_tarski(A_407, B_408))), inference(resolution, [status(thm)], [c_26, c_518])).
% 7.81/2.64  tff(c_194, plain, (![D_65, A_66, B_67]: (~r2_hidden(D_65, A_66) | r2_hidden(D_65, k2_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.81/2.64  tff(c_211, plain, (![D_68, A_69]: (~r2_hidden(D_68, A_69) | r2_hidden(D_68, k1_ordinal1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_194])).
% 7.81/2.64  tff(c_70, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.81/2.64  tff(c_132, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_70])).
% 7.81/2.64  tff(c_227, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_211, c_132])).
% 7.81/2.64  tff(c_4574, plain, (~v3_ordinal1('#skF_8') | ~v1_ordinal1('#skF_7') | '#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_4204, c_227])).
% 7.81/2.64  tff(c_4694, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_66, c_4574])).
% 7.81/2.64  tff(c_4702, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_4694])).
% 7.81/2.64  tff(c_4705, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_4702])).
% 7.81/2.64  tff(c_4709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_97, c_4705])).
% 7.81/2.64  tff(c_4710, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_4694])).
% 7.81/2.64  tff(c_4714, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4710, c_132])).
% 7.81/2.64  tff(c_4721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_783, c_4714])).
% 7.81/2.64  tff(c_4722, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_76])).
% 7.81/2.64  tff(c_4724, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitLeft, [status(thm)], [c_70])).
% 7.81/2.64  tff(c_4726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4722, c_4724])).
% 7.81/2.64  tff(c_4727, plain, (~r1_ordinal1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 7.81/2.64  tff(c_86, plain, (v1_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_79])).
% 7.81/2.64  tff(c_5464, plain, (![D_496, B_497, A_498]: (r2_hidden(D_496, B_497) | r2_hidden(D_496, A_498) | ~r2_hidden(D_496, k2_xboole_0(A_498, B_497)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.81/2.64  tff(c_8058, plain, (![D_724, A_725]: (r2_hidden(D_724, k1_tarski(A_725)) | r2_hidden(D_724, A_725) | ~r2_hidden(D_724, k1_ordinal1(A_725)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_5464])).
% 7.81/2.64  tff(c_32, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.81/2.64  tff(c_8483, plain, (![D_726, A_727]: (D_726=A_727 | r2_hidden(D_726, A_727) | ~r2_hidden(D_726, k1_ordinal1(A_727)))), inference(resolution, [status(thm)], [c_8058, c_32])).
% 7.81/2.64  tff(c_8587, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_4722, c_8483])).
% 7.81/2.64  tff(c_8588, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_8587])).
% 7.81/2.64  tff(c_50, plain, (![B_24, A_21]: (r1_tarski(B_24, A_21) | ~r2_hidden(B_24, A_21) | ~v1_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.81/2.64  tff(c_8593, plain, (r1_tarski('#skF_7', '#skF_8') | ~v1_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_8588, c_50])).
% 7.81/2.64  tff(c_8600, plain, (r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8593])).
% 7.81/2.64  tff(c_56, plain, (![A_25, B_26]: (r1_ordinal1(A_25, B_26) | ~r1_tarski(A_25, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.81/2.64  tff(c_8610, plain, (r1_ordinal1('#skF_7', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_8600, c_56])).
% 7.81/2.64  tff(c_8613, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_8610])).
% 7.81/2.64  tff(c_8615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4727, c_8613])).
% 7.81/2.64  tff(c_8616, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_8587])).
% 7.81/2.64  tff(c_8621, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8616, c_4727])).
% 7.81/2.64  tff(c_8636, plain, (~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_5430, c_8621])).
% 7.81/2.64  tff(c_8640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_8636])).
% 7.81/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/2.64  
% 7.81/2.64  Inference rules
% 7.81/2.64  ----------------------
% 7.81/2.64  #Ref     : 0
% 7.81/2.64  #Sup     : 1773
% 7.81/2.64  #Fact    : 12
% 7.81/2.64  #Define  : 0
% 7.81/2.64  #Split   : 11
% 7.81/2.64  #Chain   : 0
% 7.81/2.64  #Close   : 0
% 7.81/2.64  
% 7.81/2.64  Ordering : KBO
% 7.81/2.64  
% 7.81/2.64  Simplification rules
% 7.81/2.64  ----------------------
% 7.81/2.64  #Subsume      : 258
% 7.81/2.64  #Demod        : 78
% 7.81/2.64  #Tautology    : 130
% 7.81/2.64  #SimpNegUnit  : 70
% 7.81/2.64  #BackRed      : 14
% 7.81/2.64  
% 7.81/2.64  #Partial instantiations: 0
% 7.81/2.64  #Strategies tried      : 1
% 7.81/2.64  
% 7.81/2.64  Timing (in seconds)
% 7.81/2.64  ----------------------
% 7.81/2.64  Preprocessing        : 0.32
% 7.81/2.64  Parsing              : 0.17
% 7.81/2.64  CNF conversion       : 0.03
% 7.81/2.64  Main loop            : 1.56
% 7.81/2.64  Inferencing          : 0.48
% 7.81/2.64  Reduction            : 0.43
% 7.81/2.64  Demodulation         : 0.23
% 7.81/2.64  BG Simplification    : 0.06
% 7.81/2.64  Subsumption          : 0.45
% 7.81/2.64  Abstraction          : 0.06
% 7.81/2.64  MUC search           : 0.00
% 7.81/2.64  Cooper               : 0.00
% 7.81/2.64  Total                : 1.91
% 7.81/2.64  Index Insertion      : 0.00
% 7.81/2.64  Index Deletion       : 0.00
% 7.81/2.64  Index Matching       : 0.00
% 7.81/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
