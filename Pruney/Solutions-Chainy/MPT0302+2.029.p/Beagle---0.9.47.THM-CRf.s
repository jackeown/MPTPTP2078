%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 103 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 189 expanded)
%              Number of equality atoms :   19 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_74,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_40,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_318,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_2'(A_101,B_102),B_102)
      | r2_hidden('#skF_3'(A_101,B_102),A_101)
      | B_102 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_61,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    ! [A_19,C_32] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_32,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_61])).

tff(c_66,plain,(
    ! [C_32] : ~ r2_hidden(C_32,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64])).

tff(c_347,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_102),B_102)
      | k1_xboole_0 = B_102 ) ),
    inference(resolution,[status(thm)],[c_318,c_66])).

tff(c_450,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( r2_hidden(k4_tarski(A_114,B_115),k2_zfmisc_1(C_116,D_117))
      | ~ r2_hidden(B_115,D_117)
      | ~ r2_hidden(A_114,C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    k2_zfmisc_1('#skF_7','#skF_6') = k2_zfmisc_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_186,plain,(
    ! [B_65,D_66,A_67,C_68] :
      ( r2_hidden(B_65,D_66)
      | ~ r2_hidden(k4_tarski(A_67,B_65),k2_zfmisc_1(C_68,D_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_189,plain,(
    ! [B_65,A_67] :
      ( r2_hidden(B_65,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_67,B_65),k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_186])).

tff(c_470,plain,(
    ! [B_115,A_114] :
      ( r2_hidden(B_115,'#skF_6')
      | ~ r2_hidden(B_115,'#skF_7')
      | ~ r2_hidden(A_114,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_450,c_189])).

tff(c_477,plain,(
    ! [A_118] : ~ r2_hidden(A_118,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_489,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_347,c_477])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_489])).

tff(c_519,plain,(
    ! [B_119] :
      ( r2_hidden(B_119,'#skF_6')
      | ~ r2_hidden(B_119,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_582,plain,(
    ! [B_121] :
      ( r2_hidden('#skF_1'('#skF_7',B_121),'#skF_6')
      | r1_tarski('#skF_7',B_121) ) ),
    inference(resolution,[status(thm)],[c_6,c_519])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_590,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_582,c_4])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_5'(A_16,B_17),B_17)
      | ~ r2_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_595,plain,(
    ! [A_122,B_123] :
      ( r2_hidden(k4_tarski(A_122,B_123),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(B_123,'#skF_6')
      | ~ r2_hidden(A_122,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_450])).

tff(c_36,plain,(
    ! [B_22,D_24,A_21,C_23] :
      ( r2_hidden(B_22,D_24)
      | ~ r2_hidden(k4_tarski(A_21,B_22),k2_zfmisc_1(C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_612,plain,(
    ! [B_123,A_122] :
      ( r2_hidden(B_123,'#skF_7')
      | ~ r2_hidden(B_123,'#skF_6')
      | ~ r2_hidden(A_122,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_595,c_36])).

tff(c_643,plain,(
    ! [A_125] : ~ r2_hidden(A_125,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_612])).

tff(c_659,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_347,c_643])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_659])).

tff(c_690,plain,(
    ! [B_126] :
      ( r2_hidden(B_126,'#skF_7')
      | ~ r2_hidden(B_126,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_612])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden('#skF_5'(A_16,B_17),A_16)
      | ~ r2_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_717,plain,(
    ! [B_127] :
      ( ~ r2_xboole_0('#skF_7',B_127)
      | ~ r2_hidden('#skF_5'('#skF_7',B_127),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_690,c_26])).

tff(c_732,plain,(
    ~ r2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_717])).

tff(c_735,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_732])).

tff(c_738,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_735])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.46  
% 2.84/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.46  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.84/1.46  
% 2.84/1.46  %Foreground sorts:
% 2.84/1.46  
% 2.84/1.46  
% 2.84/1.46  %Background operators:
% 2.84/1.46  
% 2.84/1.46  
% 2.84/1.46  %Foreground operators:
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.84/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.84/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.46  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.84/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.84/1.46  
% 2.84/1.47  tff(f_89, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.84/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.84/1.47  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.84/1.47  tff(f_74, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.84/1.47  tff(f_72, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.84/1.47  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.84/1.47  tff(f_80, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.84/1.47  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.84/1.47  tff(f_70, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.84/1.47  tff(c_40, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.84/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.47  tff(c_44, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.84/1.47  tff(c_318, plain, (![A_101, B_102]: (r2_hidden('#skF_2'(A_101, B_102), B_102) | r2_hidden('#skF_3'(A_101, B_102), A_101) | B_102=A_101)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.84/1.47  tff(c_32, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.47  tff(c_30, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.47  tff(c_61, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.47  tff(c_64, plain, (![A_19, C_32]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_61])).
% 2.84/1.47  tff(c_66, plain, (![C_32]: (~r2_hidden(C_32, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64])).
% 2.84/1.47  tff(c_347, plain, (![B_102]: (r2_hidden('#skF_2'(k1_xboole_0, B_102), B_102) | k1_xboole_0=B_102)), inference(resolution, [status(thm)], [c_318, c_66])).
% 2.84/1.47  tff(c_450, plain, (![A_114, B_115, C_116, D_117]: (r2_hidden(k4_tarski(A_114, B_115), k2_zfmisc_1(C_116, D_117)) | ~r2_hidden(B_115, D_117) | ~r2_hidden(A_114, C_116))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.47  tff(c_46, plain, (k2_zfmisc_1('#skF_7', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.84/1.47  tff(c_186, plain, (![B_65, D_66, A_67, C_68]: (r2_hidden(B_65, D_66) | ~r2_hidden(k4_tarski(A_67, B_65), k2_zfmisc_1(C_68, D_66)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.47  tff(c_189, plain, (![B_65, A_67]: (r2_hidden(B_65, '#skF_6') | ~r2_hidden(k4_tarski(A_67, B_65), k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_186])).
% 2.84/1.47  tff(c_470, plain, (![B_115, A_114]: (r2_hidden(B_115, '#skF_6') | ~r2_hidden(B_115, '#skF_7') | ~r2_hidden(A_114, '#skF_6'))), inference(resolution, [status(thm)], [c_450, c_189])).
% 2.84/1.47  tff(c_477, plain, (![A_118]: (~r2_hidden(A_118, '#skF_6'))), inference(splitLeft, [status(thm)], [c_470])).
% 2.84/1.47  tff(c_489, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_347, c_477])).
% 2.84/1.47  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_489])).
% 2.84/1.47  tff(c_519, plain, (![B_119]: (r2_hidden(B_119, '#skF_6') | ~r2_hidden(B_119, '#skF_7'))), inference(splitRight, [status(thm)], [c_470])).
% 2.84/1.47  tff(c_582, plain, (![B_121]: (r2_hidden('#skF_1'('#skF_7', B_121), '#skF_6') | r1_tarski('#skF_7', B_121))), inference(resolution, [status(thm)], [c_6, c_519])).
% 2.84/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.47  tff(c_590, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_582, c_4])).
% 2.84/1.47  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.47  tff(c_28, plain, (![A_16, B_17]: (r2_hidden('#skF_5'(A_16, B_17), B_17) | ~r2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.84/1.47  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.84/1.47  tff(c_595, plain, (![A_122, B_123]: (r2_hidden(k4_tarski(A_122, B_123), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(B_123, '#skF_6') | ~r2_hidden(A_122, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_450])).
% 2.84/1.47  tff(c_36, plain, (![B_22, D_24, A_21, C_23]: (r2_hidden(B_22, D_24) | ~r2_hidden(k4_tarski(A_21, B_22), k2_zfmisc_1(C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.47  tff(c_612, plain, (![B_123, A_122]: (r2_hidden(B_123, '#skF_7') | ~r2_hidden(B_123, '#skF_6') | ~r2_hidden(A_122, '#skF_7'))), inference(resolution, [status(thm)], [c_595, c_36])).
% 2.84/1.47  tff(c_643, plain, (![A_125]: (~r2_hidden(A_125, '#skF_7'))), inference(splitLeft, [status(thm)], [c_612])).
% 2.84/1.47  tff(c_659, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_347, c_643])).
% 2.84/1.47  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_659])).
% 2.84/1.47  tff(c_690, plain, (![B_126]: (r2_hidden(B_126, '#skF_7') | ~r2_hidden(B_126, '#skF_6'))), inference(splitRight, [status(thm)], [c_612])).
% 2.84/1.47  tff(c_26, plain, (![A_16, B_17]: (~r2_hidden('#skF_5'(A_16, B_17), A_16) | ~r2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.84/1.47  tff(c_717, plain, (![B_127]: (~r2_xboole_0('#skF_7', B_127) | ~r2_hidden('#skF_5'('#skF_7', B_127), '#skF_6'))), inference(resolution, [status(thm)], [c_690, c_26])).
% 2.84/1.47  tff(c_732, plain, (~r2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_28, c_717])).
% 2.84/1.47  tff(c_735, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_8, c_732])).
% 2.84/1.47  tff(c_738, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_590, c_735])).
% 2.84/1.47  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_738])).
% 2.84/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.47  
% 2.84/1.47  Inference rules
% 2.84/1.47  ----------------------
% 2.84/1.47  #Ref     : 0
% 2.84/1.47  #Sup     : 139
% 2.84/1.47  #Fact    : 0
% 2.84/1.47  #Define  : 0
% 2.84/1.47  #Split   : 2
% 2.84/1.47  #Chain   : 0
% 2.84/1.47  #Close   : 0
% 2.84/1.47  
% 2.84/1.47  Ordering : KBO
% 2.84/1.47  
% 2.84/1.47  Simplification rules
% 2.84/1.47  ----------------------
% 2.84/1.47  #Subsume      : 34
% 2.84/1.47  #Demod        : 17
% 2.84/1.47  #Tautology    : 27
% 2.84/1.47  #SimpNegUnit  : 10
% 2.84/1.47  #BackRed      : 2
% 2.84/1.47  
% 2.84/1.47  #Partial instantiations: 0
% 2.84/1.47  #Strategies tried      : 1
% 2.84/1.47  
% 2.84/1.47  Timing (in seconds)
% 2.84/1.47  ----------------------
% 2.84/1.48  Preprocessing        : 0.36
% 2.84/1.48  Parsing              : 0.18
% 2.84/1.48  CNF conversion       : 0.03
% 2.84/1.48  Main loop            : 0.32
% 2.84/1.48  Inferencing          : 0.13
% 2.84/1.48  Reduction            : 0.08
% 2.84/1.48  Demodulation         : 0.05
% 2.84/1.48  BG Simplification    : 0.02
% 2.84/1.48  Subsumption          : 0.07
% 2.84/1.48  Abstraction          : 0.01
% 2.84/1.48  MUC search           : 0.00
% 2.84/1.48  Cooper               : 0.00
% 2.84/1.48  Total                : 0.72
% 2.84/1.48  Index Insertion      : 0.00
% 2.84/1.48  Index Deletion       : 0.00
% 2.84/1.48  Index Matching       : 0.00
% 2.84/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
