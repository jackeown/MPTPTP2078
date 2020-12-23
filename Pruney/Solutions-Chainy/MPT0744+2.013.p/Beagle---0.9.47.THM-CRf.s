%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:16 EST 2020

% Result     : Theorem 30.36s
% Output     : CNFRefutation 30.36s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 126 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 259 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_65,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_68,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69341,plain,(
    ! [A_27793,B_27794] :
      ( r1_ordinal1(A_27793,B_27794)
      | ~ r1_tarski(A_27793,B_27794)
      | ~ v3_ordinal1(B_27794)
      | ~ v3_ordinal1(A_27793) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69345,plain,(
    ! [B_10] :
      ( r1_ordinal1(B_10,B_10)
      | ~ v3_ordinal1(B_10) ) ),
    inference(resolution,[status(thm)],[c_26,c_69341])).

tff(c_30,plain,(
    ! [C_15] : r2_hidden(C_15,k1_tarski(C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_tarski(A_23)) = k1_ordinal1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_256,plain,(
    ! [D_62,B_63,A_64] :
      ( ~ r2_hidden(D_62,B_63)
      | r2_hidden(D_62,k2_xboole_0(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_780,plain,(
    ! [D_113,A_114] :
      ( ~ r2_hidden(D_113,k1_tarski(A_114))
      | r2_hidden(D_113,k1_ordinal1(A_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_256])).

tff(c_789,plain,(
    ! [C_15] : r2_hidden(C_15,k1_ordinal1(C_15)) ),
    inference(resolution,[status(thm)],[c_30,c_780])).

tff(c_70,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_598,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | r1_ordinal1(A_107,B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_138,plain,(
    ! [D_47,A_48,B_49] :
      ( ~ r2_hidden(D_47,A_48)
      | r2_hidden(D_47,k2_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,(
    ! [D_55,A_56] :
      ( ~ r2_hidden(D_55,A_56)
      | r2_hidden(D_55,k1_ordinal1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_138])).

tff(c_78,plain,
    ( r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | r1_ordinal1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_117,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( ~ r1_ordinal1('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_137,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_72])).

tff(c_210,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_182,c_137])).

tff(c_674,plain,
    ( r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_598,c_210])).

tff(c_725,plain,(
    r1_ordinal1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_674])).

tff(c_64,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_ordinal1(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_476,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,B_88)
      | ~ r1_ordinal1(A_87,B_88)
      | ~ v3_ordinal1(B_88)
      | ~ v3_ordinal1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6919,plain,(
    ! [B_4612,A_4613] :
      ( B_4612 = A_4613
      | ~ r1_tarski(B_4612,A_4613)
      | ~ r1_ordinal1(A_4613,B_4612)
      | ~ v3_ordinal1(B_4612)
      | ~ v3_ordinal1(A_4613) ) ),
    inference(resolution,[status(thm)],[c_476,c_22])).

tff(c_68812,plain,(
    ! [B_27719,A_27720] :
      ( B_27719 = A_27720
      | ~ r1_ordinal1(B_27719,A_27720)
      | ~ r1_ordinal1(A_27720,B_27719)
      | ~ v3_ordinal1(B_27719)
      | ~ v3_ordinal1(A_27720) ) ),
    inference(resolution,[status(thm)],[c_64,c_6919])).

tff(c_68848,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_ordinal1('#skF_8','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_117,c_68812])).

tff(c_68871,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_725,c_68848])).

tff(c_68880,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68871,c_137])).

tff(c_68885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_68880])).

tff(c_68887,plain,(
    ~ r1_ordinal1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_68886,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_69795,plain,(
    ! [D_28914,B_28915,A_28916] :
      ( r2_hidden(D_28914,B_28915)
      | r2_hidden(D_28914,A_28916)
      | ~ r2_hidden(D_28914,k2_xboole_0(A_28916,B_28915)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74007,plain,(
    ! [D_31609,A_31610] :
      ( r2_hidden(D_31609,k1_tarski(A_31610))
      | r2_hidden(D_31609,A_31610)
      | ~ r2_hidden(D_31609,k1_ordinal1(A_31610)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_69795])).

tff(c_28,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74663,plain,(
    ! [D_31633,A_31634] :
      ( D_31633 = A_31634
      | r2_hidden(D_31633,A_31634)
      | ~ r2_hidden(D_31633,k1_ordinal1(A_31634)) ) ),
    inference(resolution,[status(thm)],[c_74007,c_28])).

tff(c_74732,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_68886,c_74663])).

tff(c_74733,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74732])).

tff(c_69126,plain,(
    ! [B_27780,A_27781] :
      ( r2_hidden(B_27780,A_27781)
      | r1_ordinal1(A_27781,B_27780)
      | ~ v3_ordinal1(B_27780)
      | ~ v3_ordinal1(A_27781) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_69201,plain,(
    ! [A_27781,B_27780] :
      ( ~ r2_hidden(A_27781,B_27780)
      | r1_ordinal1(A_27781,B_27780)
      | ~ v3_ordinal1(B_27780)
      | ~ v3_ordinal1(A_27781) ) ),
    inference(resolution,[status(thm)],[c_69126,c_2])).

tff(c_74736,plain,
    ( r1_ordinal1('#skF_7','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_74733,c_69201])).

tff(c_74741,plain,(
    r1_ordinal1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_74736])).

tff(c_74743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68887,c_74741])).

tff(c_74744,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74732])).

tff(c_74750,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74744,c_68887])).

tff(c_74771,plain,(
    ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_69345,c_74750])).

tff(c_74775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_74771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:52:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.36/20.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.36/20.26  
% 30.36/20.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.36/20.26  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4
% 30.36/20.26  
% 30.36/20.26  %Foreground sorts:
% 30.36/20.26  
% 30.36/20.26  
% 30.36/20.26  %Background operators:
% 30.36/20.26  
% 30.36/20.26  
% 30.36/20.26  %Foreground operators:
% 30.36/20.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 30.36/20.26  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 30.36/20.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.36/20.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.36/20.26  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 30.36/20.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 30.36/20.26  tff('#skF_7', type, '#skF_7': $i).
% 30.36/20.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 30.36/20.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.36/20.26  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 30.36/20.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 30.36/20.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 30.36/20.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.36/20.26  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 30.36/20.26  tff('#skF_8', type, '#skF_8': $i).
% 30.36/20.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.36/20.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.36/20.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.36/20.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 30.36/20.26  
% 30.36/20.28  tff(f_92, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 30.36/20.28  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.36/20.28  tff(f_73, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 30.36/20.28  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 30.36/20.28  tff(f_65, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 30.36/20.28  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 30.36/20.28  tff(f_82, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 30.36/20.28  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 30.36/20.28  tff(c_68, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.36/20.28  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.36/20.28  tff(c_69341, plain, (![A_27793, B_27794]: (r1_ordinal1(A_27793, B_27794) | ~r1_tarski(A_27793, B_27794) | ~v3_ordinal1(B_27794) | ~v3_ordinal1(A_27793))), inference(cnfTransformation, [status(thm)], [f_73])).
% 30.36/20.28  tff(c_69345, plain, (![B_10]: (r1_ordinal1(B_10, B_10) | ~v3_ordinal1(B_10))), inference(resolution, [status(thm)], [c_26, c_69341])).
% 30.36/20.28  tff(c_30, plain, (![C_15]: (r2_hidden(C_15, k1_tarski(C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.36/20.28  tff(c_60, plain, (![A_23]: (k2_xboole_0(A_23, k1_tarski(A_23))=k1_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 30.36/20.28  tff(c_256, plain, (![D_62, B_63, A_64]: (~r2_hidden(D_62, B_63) | r2_hidden(D_62, k2_xboole_0(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.36/20.28  tff(c_780, plain, (![D_113, A_114]: (~r2_hidden(D_113, k1_tarski(A_114)) | r2_hidden(D_113, k1_ordinal1(A_114)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_256])).
% 30.36/20.28  tff(c_789, plain, (![C_15]: (r2_hidden(C_15, k1_ordinal1(C_15)))), inference(resolution, [status(thm)], [c_30, c_780])).
% 30.36/20.28  tff(c_70, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.36/20.28  tff(c_598, plain, (![B_106, A_107]: (r2_hidden(B_106, A_107) | r1_ordinal1(A_107, B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_107))), inference(cnfTransformation, [status(thm)], [f_82])).
% 30.36/20.28  tff(c_138, plain, (![D_47, A_48, B_49]: (~r2_hidden(D_47, A_48) | r2_hidden(D_47, k2_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.36/20.28  tff(c_182, plain, (![D_55, A_56]: (~r2_hidden(D_55, A_56) | r2_hidden(D_55, k1_ordinal1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_138])).
% 30.36/20.28  tff(c_78, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | r1_ordinal1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.36/20.28  tff(c_117, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 30.36/20.28  tff(c_72, plain, (~r1_ordinal1('#skF_7', '#skF_8') | ~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.36/20.28  tff(c_137, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_72])).
% 30.36/20.28  tff(c_210, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_182, c_137])).
% 30.36/20.28  tff(c_674, plain, (r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_598, c_210])).
% 30.36/20.28  tff(c_725, plain, (r1_ordinal1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_674])).
% 30.36/20.28  tff(c_64, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~r1_ordinal1(A_24, B_25) | ~v3_ordinal1(B_25) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 30.36/20.28  tff(c_476, plain, (![A_87, B_88]: (r1_tarski(A_87, B_88) | ~r1_ordinal1(A_87, B_88) | ~v3_ordinal1(B_88) | ~v3_ordinal1(A_87))), inference(cnfTransformation, [status(thm)], [f_73])).
% 30.36/20.28  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.36/20.28  tff(c_6919, plain, (![B_4612, A_4613]: (B_4612=A_4613 | ~r1_tarski(B_4612, A_4613) | ~r1_ordinal1(A_4613, B_4612) | ~v3_ordinal1(B_4612) | ~v3_ordinal1(A_4613))), inference(resolution, [status(thm)], [c_476, c_22])).
% 30.36/20.28  tff(c_68812, plain, (![B_27719, A_27720]: (B_27719=A_27720 | ~r1_ordinal1(B_27719, A_27720) | ~r1_ordinal1(A_27720, B_27719) | ~v3_ordinal1(B_27719) | ~v3_ordinal1(A_27720))), inference(resolution, [status(thm)], [c_64, c_6919])).
% 30.36/20.28  tff(c_68848, plain, ('#skF_7'='#skF_8' | ~r1_ordinal1('#skF_8', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_117, c_68812])).
% 30.36/20.28  tff(c_68871, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_725, c_68848])).
% 30.36/20.28  tff(c_68880, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68871, c_137])).
% 30.36/20.28  tff(c_68885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_789, c_68880])).
% 30.36/20.28  tff(c_68887, plain, (~r1_ordinal1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 30.36/20.28  tff(c_68886, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_78])).
% 30.36/20.28  tff(c_69795, plain, (![D_28914, B_28915, A_28916]: (r2_hidden(D_28914, B_28915) | r2_hidden(D_28914, A_28916) | ~r2_hidden(D_28914, k2_xboole_0(A_28916, B_28915)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.36/20.28  tff(c_74007, plain, (![D_31609, A_31610]: (r2_hidden(D_31609, k1_tarski(A_31610)) | r2_hidden(D_31609, A_31610) | ~r2_hidden(D_31609, k1_ordinal1(A_31610)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_69795])).
% 30.36/20.28  tff(c_28, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.36/20.28  tff(c_74663, plain, (![D_31633, A_31634]: (D_31633=A_31634 | r2_hidden(D_31633, A_31634) | ~r2_hidden(D_31633, k1_ordinal1(A_31634)))), inference(resolution, [status(thm)], [c_74007, c_28])).
% 30.36/20.28  tff(c_74732, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_68886, c_74663])).
% 30.36/20.28  tff(c_74733, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_74732])).
% 30.36/20.28  tff(c_69126, plain, (![B_27780, A_27781]: (r2_hidden(B_27780, A_27781) | r1_ordinal1(A_27781, B_27780) | ~v3_ordinal1(B_27780) | ~v3_ordinal1(A_27781))), inference(cnfTransformation, [status(thm)], [f_82])).
% 30.36/20.28  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 30.36/20.28  tff(c_69201, plain, (![A_27781, B_27780]: (~r2_hidden(A_27781, B_27780) | r1_ordinal1(A_27781, B_27780) | ~v3_ordinal1(B_27780) | ~v3_ordinal1(A_27781))), inference(resolution, [status(thm)], [c_69126, c_2])).
% 30.36/20.28  tff(c_74736, plain, (r1_ordinal1('#skF_7', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_74733, c_69201])).
% 30.36/20.28  tff(c_74741, plain, (r1_ordinal1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_74736])).
% 30.36/20.28  tff(c_74743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68887, c_74741])).
% 30.36/20.28  tff(c_74744, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_74732])).
% 30.36/20.28  tff(c_74750, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74744, c_68887])).
% 30.36/20.28  tff(c_74771, plain, (~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_69345, c_74750])).
% 30.36/20.28  tff(c_74775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_74771])).
% 30.36/20.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.36/20.28  
% 30.36/20.28  Inference rules
% 30.36/20.28  ----------------------
% 30.36/20.28  #Ref     : 0
% 30.36/20.28  #Sup     : 15120
% 30.36/20.28  #Fact    : 56
% 30.36/20.28  #Define  : 0
% 30.36/20.28  #Split   : 10
% 30.36/20.28  #Chain   : 0
% 30.36/20.28  #Close   : 0
% 30.36/20.28  
% 30.36/20.28  Ordering : KBO
% 30.36/20.28  
% 30.36/20.28  Simplification rules
% 30.36/20.28  ----------------------
% 30.36/20.28  #Subsume      : 5306
% 30.36/20.28  #Demod        : 856
% 30.36/20.28  #Tautology    : 388
% 30.36/20.28  #SimpNegUnit  : 226
% 30.36/20.28  #BackRed      : 19
% 30.36/20.28  
% 30.36/20.28  #Partial instantiations: 15324
% 30.36/20.28  #Strategies tried      : 1
% 30.36/20.28  
% 30.36/20.28  Timing (in seconds)
% 30.36/20.28  ----------------------
% 30.36/20.28  Preprocessing        : 0.31
% 30.36/20.28  Parsing              : 0.15
% 30.36/20.28  CNF conversion       : 0.02
% 30.36/20.28  Main loop            : 19.20
% 30.53/20.28  Inferencing          : 2.39
% 30.53/20.28  Reduction            : 6.86
% 30.53/20.28  Demodulation         : 2.08
% 30.53/20.28  BG Simplification    : 0.25
% 30.53/20.28  Subsumption          : 8.61
% 30.53/20.28  Abstraction          : 0.47
% 30.53/20.28  MUC search           : 0.00
% 30.53/20.28  Cooper               : 0.00
% 30.53/20.28  Total                : 19.54
% 30.53/20.28  Index Insertion      : 0.00
% 30.53/20.28  Index Deletion       : 0.00
% 30.53/20.28  Index Matching       : 0.00
% 30.53/20.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
