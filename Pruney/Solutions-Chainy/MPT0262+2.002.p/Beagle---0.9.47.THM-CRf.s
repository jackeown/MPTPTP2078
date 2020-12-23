%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:13 EST 2020

% Result     : Theorem 11.32s
% Output     : CNFRefutation 11.32s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 221 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :   92 ( 505 expanded)
%              Number of equality atoms :   20 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_88,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),A_39)
      | r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_95,plain,(
    ! [A_44,B_45] :
      ( '#skF_1'(k1_tarski(A_44),B_45) = A_44
      | r1_xboole_0(k1_tarski(A_44),B_45) ) ),
    inference(resolution,[status(thm)],[c_88,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [B_45,A_44] :
      ( r1_xboole_0(B_45,k1_tarski(A_44))
      | '#skF_1'(k1_tarski(A_44),B_45) = A_44 ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_28,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_112,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ r1_xboole_0(A_46,C_47)
      | ~ r1_xboole_0(A_46,B_48)
      | r1_xboole_0(A_46,k2_xboole_0(B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_435,plain,(
    ! [A_98,B_99,A_100] :
      ( ~ r1_xboole_0(A_98,k1_tarski(B_99))
      | ~ r1_xboole_0(A_98,k1_tarski(A_100))
      | r1_xboole_0(A_98,k2_tarski(A_100,B_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_112])).

tff(c_894,plain,(
    ! [A_130,B_131,A_132] :
      ( r1_xboole_0(k2_tarski(A_130,B_131),A_132)
      | ~ r1_xboole_0(A_132,k1_tarski(B_131))
      | ~ r1_xboole_0(A_132,k1_tarski(A_130)) ) ),
    inference(resolution,[status(thm)],[c_435,c_2])).

tff(c_1029,plain,(
    ! [A_142,A_143,B_144] :
      ( r1_xboole_0(k2_tarski(A_142,A_143),B_144)
      | ~ r1_xboole_0(B_144,k1_tarski(A_142))
      | '#skF_1'(k1_tarski(A_143),B_144) = A_143 ) ),
    inference(resolution,[status(thm)],[c_111,c_894])).

tff(c_21128,plain,(
    ! [A_3349,A_3350,B_3351] :
      ( r1_xboole_0(k2_tarski(A_3349,A_3350),B_3351)
      | '#skF_1'(k1_tarski(A_3350),B_3351) = A_3350
      | '#skF_1'(k1_tarski(A_3349),B_3351) = A_3349 ) ),
    inference(resolution,[status(thm)],[c_111,c_1029])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_21203,plain,
    ( '#skF_1'(k1_tarski('#skF_6'),'#skF_5') = '#skF_6'
    | '#skF_1'(k1_tarski('#skF_4'),'#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21128,c_34])).

tff(c_21204,plain,(
    '#skF_1'(k1_tarski('#skF_4'),'#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_21203])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_21253,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_21204,c_6])).

tff(c_21270,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_21253])).

tff(c_21277,plain,(
    r1_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21270,c_2])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_35)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,(
    ! [A_34,A_11] :
      ( '#skF_1'(A_34,k1_tarski(A_11)) = A_11
      | r1_xboole_0(A_34,k1_tarski(A_11)) ) ),
    inference(resolution,[status(thm)],[c_78,c_16])).

tff(c_935,plain,(
    ! [A_130,A_11,A_34] :
      ( r1_xboole_0(k2_tarski(A_130,A_11),A_34)
      | ~ r1_xboole_0(A_34,k1_tarski(A_130))
      | '#skF_1'(A_34,k1_tarski(A_11)) = A_11 ) ),
    inference(resolution,[status(thm)],[c_83,c_894])).

tff(c_21537,plain,(
    ! [A_3357] :
      ( r1_xboole_0(k2_tarski('#skF_4',A_3357),'#skF_5')
      | '#skF_1'('#skF_5',k1_tarski(A_3357)) = A_3357 ) ),
    inference(resolution,[status(thm)],[c_21277,c_935])).

tff(c_21570,plain,(
    '#skF_1'('#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_21537,c_34])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_21617,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21570,c_8])).

tff(c_21636,plain,(
    r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_21617])).

tff(c_452,plain,(
    ! [A_100,B_99,A_98] :
      ( r1_xboole_0(k2_tarski(A_100,B_99),A_98)
      | ~ r1_xboole_0(A_98,k1_tarski(B_99))
      | ~ r1_xboole_0(A_98,k1_tarski(A_100)) ) ),
    inference(resolution,[status(thm)],[c_435,c_2])).

tff(c_21696,plain,(
    ! [A_3359] :
      ( r1_xboole_0(k2_tarski(A_3359,'#skF_6'),'#skF_5')
      | ~ r1_xboole_0('#skF_5',k1_tarski(A_3359)) ) ),
    inference(resolution,[status(thm)],[c_21636,c_452])).

tff(c_21715,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21696,c_34])).

tff(c_21732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21277,c_21715])).

tff(c_21734,plain,(
    '#skF_1'(k1_tarski('#skF_4'),'#skF_5') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21203])).

tff(c_21733,plain,(
    '#skF_1'(k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_21203])).

tff(c_21783,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_21733,c_6])).

tff(c_21800,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_21783])).

tff(c_21807,plain,(
    r1_xboole_0('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_21800,c_2])).

tff(c_21863,plain,(
    ! [A_3361] :
      ( r1_xboole_0(k2_tarski(A_3361,'#skF_6'),'#skF_5')
      | ~ r1_xboole_0('#skF_5',k1_tarski(A_3361)) ) ),
    inference(resolution,[status(thm)],[c_21807,c_452])).

tff(c_21896,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21863,c_34])).

tff(c_21901,plain,(
    '#skF_1'(k1_tarski('#skF_4'),'#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_111,c_21896])).

tff(c_21908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21734,c_21901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.32/3.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.32/3.99  
% 11.32/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.32/4.00  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 11.32/4.00  
% 11.32/4.00  %Foreground sorts:
% 11.32/4.00  
% 11.32/4.00  
% 11.32/4.00  %Background operators:
% 11.32/4.00  
% 11.32/4.00  
% 11.32/4.00  %Foreground operators:
% 11.32/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.32/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.32/4.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.32/4.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.32/4.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.32/4.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.32/4.00  tff('#skF_5', type, '#skF_5': $i).
% 11.32/4.00  tff('#skF_6', type, '#skF_6': $i).
% 11.32/4.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.32/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.32/4.00  tff('#skF_4', type, '#skF_4': $i).
% 11.32/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.32/4.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.32/4.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.32/4.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.32/4.00  
% 11.32/4.01  tff(f_87, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 11.32/4.01  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.32/4.01  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 11.32/4.01  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.32/4.01  tff(f_72, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 11.32/4.01  tff(f_63, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 11.32/4.01  tff(c_38, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.32/4.01  tff(c_88, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), A_39) | r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.32/4.01  tff(c_16, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.32/4.01  tff(c_95, plain, (![A_44, B_45]: ('#skF_1'(k1_tarski(A_44), B_45)=A_44 | r1_xboole_0(k1_tarski(A_44), B_45))), inference(resolution, [status(thm)], [c_88, c_16])).
% 11.32/4.01  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.32/4.01  tff(c_111, plain, (![B_45, A_44]: (r1_xboole_0(B_45, k1_tarski(A_44)) | '#skF_1'(k1_tarski(A_44), B_45)=A_44)), inference(resolution, [status(thm)], [c_95, c_2])).
% 11.32/4.01  tff(c_28, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.32/4.01  tff(c_112, plain, (![A_46, C_47, B_48]: (~r1_xboole_0(A_46, C_47) | ~r1_xboole_0(A_46, B_48) | r1_xboole_0(A_46, k2_xboole_0(B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.32/4.01  tff(c_435, plain, (![A_98, B_99, A_100]: (~r1_xboole_0(A_98, k1_tarski(B_99)) | ~r1_xboole_0(A_98, k1_tarski(A_100)) | r1_xboole_0(A_98, k2_tarski(A_100, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_112])).
% 11.32/4.01  tff(c_894, plain, (![A_130, B_131, A_132]: (r1_xboole_0(k2_tarski(A_130, B_131), A_132) | ~r1_xboole_0(A_132, k1_tarski(B_131)) | ~r1_xboole_0(A_132, k1_tarski(A_130)))), inference(resolution, [status(thm)], [c_435, c_2])).
% 11.32/4.01  tff(c_1029, plain, (![A_142, A_143, B_144]: (r1_xboole_0(k2_tarski(A_142, A_143), B_144) | ~r1_xboole_0(B_144, k1_tarski(A_142)) | '#skF_1'(k1_tarski(A_143), B_144)=A_143)), inference(resolution, [status(thm)], [c_111, c_894])).
% 11.32/4.01  tff(c_21128, plain, (![A_3349, A_3350, B_3351]: (r1_xboole_0(k2_tarski(A_3349, A_3350), B_3351) | '#skF_1'(k1_tarski(A_3350), B_3351)=A_3350 | '#skF_1'(k1_tarski(A_3349), B_3351)=A_3349)), inference(resolution, [status(thm)], [c_111, c_1029])).
% 11.32/4.01  tff(c_34, plain, (~r1_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.32/4.01  tff(c_21203, plain, ('#skF_1'(k1_tarski('#skF_6'), '#skF_5')='#skF_6' | '#skF_1'(k1_tarski('#skF_4'), '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_21128, c_34])).
% 11.32/4.01  tff(c_21204, plain, ('#skF_1'(k1_tarski('#skF_4'), '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_21203])).
% 11.32/4.01  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.32/4.01  tff(c_21253, plain, (r2_hidden('#skF_4', '#skF_5') | r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_21204, c_6])).
% 11.32/4.01  tff(c_21270, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_21253])).
% 11.32/4.01  tff(c_21277, plain, (r1_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_21270, c_2])).
% 11.32/4.01  tff(c_36, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.32/4.01  tff(c_78, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), B_35) | r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.32/4.01  tff(c_83, plain, (![A_34, A_11]: ('#skF_1'(A_34, k1_tarski(A_11))=A_11 | r1_xboole_0(A_34, k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_78, c_16])).
% 11.32/4.01  tff(c_935, plain, (![A_130, A_11, A_34]: (r1_xboole_0(k2_tarski(A_130, A_11), A_34) | ~r1_xboole_0(A_34, k1_tarski(A_130)) | '#skF_1'(A_34, k1_tarski(A_11))=A_11)), inference(resolution, [status(thm)], [c_83, c_894])).
% 11.32/4.01  tff(c_21537, plain, (![A_3357]: (r1_xboole_0(k2_tarski('#skF_4', A_3357), '#skF_5') | '#skF_1'('#skF_5', k1_tarski(A_3357))=A_3357)), inference(resolution, [status(thm)], [c_21277, c_935])).
% 11.32/4.01  tff(c_21570, plain, ('#skF_1'('#skF_5', k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_21537, c_34])).
% 11.32/4.01  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.32/4.01  tff(c_21617, plain, (r2_hidden('#skF_6', '#skF_5') | r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21570, c_8])).
% 11.32/4.01  tff(c_21636, plain, (r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_36, c_21617])).
% 11.32/4.01  tff(c_452, plain, (![A_100, B_99, A_98]: (r1_xboole_0(k2_tarski(A_100, B_99), A_98) | ~r1_xboole_0(A_98, k1_tarski(B_99)) | ~r1_xboole_0(A_98, k1_tarski(A_100)))), inference(resolution, [status(thm)], [c_435, c_2])).
% 11.32/4.01  tff(c_21696, plain, (![A_3359]: (r1_xboole_0(k2_tarski(A_3359, '#skF_6'), '#skF_5') | ~r1_xboole_0('#skF_5', k1_tarski(A_3359)))), inference(resolution, [status(thm)], [c_21636, c_452])).
% 11.32/4.01  tff(c_21715, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_21696, c_34])).
% 11.32/4.01  tff(c_21732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21277, c_21715])).
% 11.32/4.01  tff(c_21734, plain, ('#skF_1'(k1_tarski('#skF_4'), '#skF_5')!='#skF_4'), inference(splitRight, [status(thm)], [c_21203])).
% 11.32/4.01  tff(c_21733, plain, ('#skF_1'(k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_21203])).
% 11.32/4.01  tff(c_21783, plain, (r2_hidden('#skF_6', '#skF_5') | r1_xboole_0(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_21733, c_6])).
% 11.32/4.01  tff(c_21800, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_21783])).
% 11.32/4.01  tff(c_21807, plain, (r1_xboole_0('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_21800, c_2])).
% 11.32/4.01  tff(c_21863, plain, (![A_3361]: (r1_xboole_0(k2_tarski(A_3361, '#skF_6'), '#skF_5') | ~r1_xboole_0('#skF_5', k1_tarski(A_3361)))), inference(resolution, [status(thm)], [c_21807, c_452])).
% 11.32/4.01  tff(c_21896, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_21863, c_34])).
% 11.32/4.01  tff(c_21901, plain, ('#skF_1'(k1_tarski('#skF_4'), '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_111, c_21896])).
% 11.32/4.01  tff(c_21908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21734, c_21901])).
% 11.32/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.32/4.01  
% 11.32/4.01  Inference rules
% 11.32/4.01  ----------------------
% 11.32/4.01  #Ref     : 0
% 11.32/4.01  #Sup     : 4668
% 11.32/4.01  #Fact    : 2
% 11.32/4.01  #Define  : 0
% 11.32/4.01  #Split   : 1
% 11.32/4.01  #Chain   : 0
% 11.32/4.01  #Close   : 0
% 11.32/4.01  
% 11.32/4.01  Ordering : KBO
% 11.32/4.01  
% 11.32/4.01  Simplification rules
% 11.32/4.01  ----------------------
% 11.32/4.01  #Subsume      : 915
% 11.32/4.01  #Demod        : 570
% 11.32/4.01  #Tautology    : 797
% 11.32/4.01  #SimpNegUnit  : 4
% 11.32/4.01  #BackRed      : 0
% 11.32/4.01  
% 11.32/4.01  #Partial instantiations: 1920
% 11.32/4.01  #Strategies tried      : 1
% 11.32/4.01  
% 11.32/4.01  Timing (in seconds)
% 11.32/4.01  ----------------------
% 11.32/4.01  Preprocessing        : 0.31
% 11.49/4.01  Parsing              : 0.16
% 11.49/4.01  CNF conversion       : 0.02
% 11.49/4.01  Main loop            : 2.95
% 11.49/4.01  Inferencing          : 0.82
% 11.49/4.01  Reduction            : 0.53
% 11.49/4.01  Demodulation         : 0.36
% 11.49/4.01  BG Simplification    : 0.12
% 11.49/4.01  Subsumption          : 1.27
% 11.49/4.01  Abstraction          : 0.18
% 11.49/4.01  MUC search           : 0.00
% 11.49/4.01  Cooper               : 0.00
% 11.49/4.01  Total                : 3.28
% 11.49/4.01  Index Insertion      : 0.00
% 11.49/4.01  Index Deletion       : 0.00
% 11.49/4.01  Index Matching       : 0.00
% 11.49/4.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
