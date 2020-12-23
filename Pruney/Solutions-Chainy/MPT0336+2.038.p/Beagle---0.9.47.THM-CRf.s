%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 176 expanded)
%              Number of equality atoms :   11 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_58,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),k3_xboole_0(A_16,B_17))
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    r1_xboole_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_341,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,B_88)
      | ~ r2_hidden(C_89,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_360,plain,(
    ! [C_90] :
      ( ~ r2_hidden(C_90,'#skF_8')
      | ~ r2_hidden(C_90,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_62,c_341])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_360])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    r1_tarski(k3_xboole_0('#skF_7','#skF_8'),k1_tarski('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_67,plain,(
    r1_tarski(k3_xboole_0('#skF_8','#skF_7'),k1_tarski('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_134,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_138,plain,(
    k3_xboole_0(k3_xboole_0('#skF_8','#skF_7'),k1_tarski('#skF_10')) = k3_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_67,c_134])).

tff(c_32,plain,(
    ! [A_16,B_17,C_20] :
      ( ~ r1_xboole_0(A_16,B_17)
      | ~ r2_hidden(C_20,k3_xboole_0(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_210,plain,(
    ! [C_20] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_8','#skF_7'),k1_tarski('#skF_10'))
      | ~ r2_hidden(C_20,k3_xboole_0('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_32])).

tff(c_663,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_8','#skF_7'),k1_tarski('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_420,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_4'(A_99,B_100),k3_xboole_0(A_99,B_100))
      | r1_xboole_0(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_451,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_4'(A_101,B_102),B_102)
      | r1_xboole_0(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_420,c_6])).

tff(c_42,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_486,plain,(
    ! [A_101,A_26] :
      ( '#skF_4'(A_101,k1_tarski(A_26)) = A_26
      | r1_xboole_0(A_101,k1_tarski(A_26)) ) ),
    inference(resolution,[status(thm)],[c_451,c_42])).

tff(c_679,plain,(
    '#skF_4'(k3_xboole_0('#skF_8','#skF_7'),k1_tarski('#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_486,c_663])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_450,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_4'(A_99,B_100),A_99)
      | r1_xboole_0(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_420,c_8])).

tff(c_687,plain,
    ( r2_hidden('#skF_10',k3_xboole_0('#skF_8','#skF_7'))
    | r1_xboole_0(k3_xboole_0('#skF_8','#skF_7'),k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_450])).

tff(c_696,plain,(
    r2_hidden('#skF_10',k3_xboole_0('#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_687])).

tff(c_716,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_696,c_8])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_716])).

tff(c_743,plain,(
    ! [C_121] : ~ r2_hidden(C_121,k3_xboole_0('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_771,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_743])).

tff(c_78,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_78])).

tff(c_728,plain,(
    ! [A_118,C_119,B_120] :
      ( ~ r1_xboole_0(A_118,C_119)
      | ~ r1_xboole_0(A_118,B_120)
      | r1_xboole_0(A_118,k2_xboole_0(B_120,C_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_959,plain,(
    ! [B_138,C_139,A_140] :
      ( r1_xboole_0(k2_xboole_0(B_138,C_139),A_140)
      | ~ r1_xboole_0(A_140,C_139)
      | ~ r1_xboole_0(A_140,B_138) ) ),
    inference(resolution,[status(thm)],[c_728,c_22])).

tff(c_60,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_7','#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_974,plain,
    ( ~ r1_xboole_0('#skF_8','#skF_9')
    | ~ r1_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_959,c_60])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_81,c_974])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:52:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.46  
% 2.86/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 2.86/1.46  
% 2.86/1.46  %Foreground sorts:
% 2.86/1.46  
% 2.86/1.46  
% 2.86/1.46  %Background operators:
% 2.86/1.46  
% 2.86/1.46  
% 2.86/1.46  %Foreground operators:
% 2.86/1.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.86/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.86/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.46  tff('#skF_10', type, '#skF_10': $i).
% 2.86/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.86/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.86/1.46  tff('#skF_9', type, '#skF_9': $i).
% 2.86/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.86/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.86/1.46  
% 3.23/1.48  tff(f_72, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.23/1.48  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.23/1.48  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.23/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.48  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.48  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.23/1.48  tff(f_99, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.23/1.48  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.23/1.48  tff(f_92, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.23/1.48  tff(c_30, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), k3_xboole_0(A_16, B_17)) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.48  tff(c_64, plain, (r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.23/1.48  tff(c_62, plain, (r1_xboole_0('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.23/1.48  tff(c_341, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, B_88) | ~r2_hidden(C_89, A_87))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.48  tff(c_360, plain, (![C_90]: (~r2_hidden(C_90, '#skF_8') | ~r2_hidden(C_90, '#skF_9'))), inference(resolution, [status(thm)], [c_62, c_341])).
% 3.23/1.48  tff(c_374, plain, (~r2_hidden('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_64, c_360])).
% 3.23/1.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.48  tff(c_66, plain, (r1_tarski(k3_xboole_0('#skF_7', '#skF_8'), k1_tarski('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.23/1.48  tff(c_67, plain, (r1_tarski(k3_xboole_0('#skF_8', '#skF_7'), k1_tarski('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 3.23/1.48  tff(c_134, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.48  tff(c_138, plain, (k3_xboole_0(k3_xboole_0('#skF_8', '#skF_7'), k1_tarski('#skF_10'))=k3_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_67, c_134])).
% 3.23/1.48  tff(c_32, plain, (![A_16, B_17, C_20]: (~r1_xboole_0(A_16, B_17) | ~r2_hidden(C_20, k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.48  tff(c_210, plain, (![C_20]: (~r1_xboole_0(k3_xboole_0('#skF_8', '#skF_7'), k1_tarski('#skF_10')) | ~r2_hidden(C_20, k3_xboole_0('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_138, c_32])).
% 3.23/1.48  tff(c_663, plain, (~r1_xboole_0(k3_xboole_0('#skF_8', '#skF_7'), k1_tarski('#skF_10'))), inference(splitLeft, [status(thm)], [c_210])).
% 3.23/1.48  tff(c_420, plain, (![A_99, B_100]: (r2_hidden('#skF_4'(A_99, B_100), k3_xboole_0(A_99, B_100)) | r1_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.48  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.48  tff(c_451, plain, (![A_101, B_102]: (r2_hidden('#skF_4'(A_101, B_102), B_102) | r1_xboole_0(A_101, B_102))), inference(resolution, [status(thm)], [c_420, c_6])).
% 3.23/1.48  tff(c_42, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.23/1.48  tff(c_486, plain, (![A_101, A_26]: ('#skF_4'(A_101, k1_tarski(A_26))=A_26 | r1_xboole_0(A_101, k1_tarski(A_26)))), inference(resolution, [status(thm)], [c_451, c_42])).
% 3.23/1.48  tff(c_679, plain, ('#skF_4'(k3_xboole_0('#skF_8', '#skF_7'), k1_tarski('#skF_10'))='#skF_10'), inference(resolution, [status(thm)], [c_486, c_663])).
% 3.23/1.48  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.48  tff(c_450, plain, (![A_99, B_100]: (r2_hidden('#skF_4'(A_99, B_100), A_99) | r1_xboole_0(A_99, B_100))), inference(resolution, [status(thm)], [c_420, c_8])).
% 3.23/1.48  tff(c_687, plain, (r2_hidden('#skF_10', k3_xboole_0('#skF_8', '#skF_7')) | r1_xboole_0(k3_xboole_0('#skF_8', '#skF_7'), k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_679, c_450])).
% 3.23/1.48  tff(c_696, plain, (r2_hidden('#skF_10', k3_xboole_0('#skF_8', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_663, c_687])).
% 3.23/1.48  tff(c_716, plain, (r2_hidden('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_696, c_8])).
% 3.23/1.48  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_374, c_716])).
% 3.23/1.48  tff(c_743, plain, (![C_121]: (~r2_hidden(C_121, k3_xboole_0('#skF_8', '#skF_7')))), inference(splitRight, [status(thm)], [c_210])).
% 3.23/1.48  tff(c_771, plain, (r1_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_30, c_743])).
% 3.23/1.48  tff(c_78, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.48  tff(c_81, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_78])).
% 3.23/1.48  tff(c_728, plain, (![A_118, C_119, B_120]: (~r1_xboole_0(A_118, C_119) | ~r1_xboole_0(A_118, B_120) | r1_xboole_0(A_118, k2_xboole_0(B_120, C_119)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.48  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.48  tff(c_959, plain, (![B_138, C_139, A_140]: (r1_xboole_0(k2_xboole_0(B_138, C_139), A_140) | ~r1_xboole_0(A_140, C_139) | ~r1_xboole_0(A_140, B_138))), inference(resolution, [status(thm)], [c_728, c_22])).
% 3.23/1.48  tff(c_60, plain, (~r1_xboole_0(k2_xboole_0('#skF_7', '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.23/1.48  tff(c_974, plain, (~r1_xboole_0('#skF_8', '#skF_9') | ~r1_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_959, c_60])).
% 3.23/1.48  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_771, c_81, c_974])).
% 3.23/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  Inference rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Ref     : 0
% 3.23/1.48  #Sup     : 212
% 3.23/1.48  #Fact    : 0
% 3.23/1.48  #Define  : 0
% 3.23/1.48  #Split   : 1
% 3.23/1.48  #Chain   : 0
% 3.23/1.48  #Close   : 0
% 3.23/1.48  
% 3.23/1.48  Ordering : KBO
% 3.23/1.48  
% 3.23/1.48  Simplification rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Subsume      : 59
% 3.23/1.48  #Demod        : 33
% 3.23/1.48  #Tautology    : 58
% 3.23/1.48  #SimpNegUnit  : 6
% 3.23/1.48  #BackRed      : 0
% 3.23/1.48  
% 3.23/1.48  #Partial instantiations: 0
% 3.23/1.48  #Strategies tried      : 1
% 3.23/1.48  
% 3.23/1.48  Timing (in seconds)
% 3.23/1.48  ----------------------
% 3.23/1.48  Preprocessing        : 0.33
% 3.23/1.48  Parsing              : 0.17
% 3.23/1.48  CNF conversion       : 0.02
% 3.23/1.48  Main loop            : 0.39
% 3.23/1.48  Inferencing          : 0.14
% 3.23/1.48  Reduction            : 0.13
% 3.23/1.48  Demodulation         : 0.09
% 3.23/1.48  BG Simplification    : 0.02
% 3.23/1.48  Subsumption          : 0.08
% 3.23/1.48  Abstraction          : 0.02
% 3.23/1.48  MUC search           : 0.00
% 3.23/1.48  Cooper               : 0.00
% 3.23/1.48  Total                : 0.75
% 3.23/1.48  Index Insertion      : 0.00
% 3.23/1.48  Index Deletion       : 0.00
% 3.23/1.48  Index Matching       : 0.00
% 3.23/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
