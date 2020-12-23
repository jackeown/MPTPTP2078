%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 111 expanded)
%              Number of equality atoms :   24 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_44,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_124,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [B_46,A_45] :
      ( r1_xboole_0(B_46,k1_tarski(A_45))
      | r2_hidden(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_46,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_299,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_xboole_0(A_67,C_68)
      | ~ r1_xboole_0(A_67,k2_xboole_0(B_69,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_321,plain,(
    ! [A_72] :
      ( r1_xboole_0(A_72,'#skF_3')
      | ~ r1_xboole_0(A_72,k1_tarski('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_299])).

tff(c_330,plain,(
    ! [B_46] :
      ( r1_xboole_0(B_46,'#skF_3')
      | r2_hidden('#skF_1',B_46) ) ),
    inference(resolution,[status(thm)],[c_131,c_321])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_67,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_67])).

tff(c_462,plain,(
    ! [B_82,A_83] :
      ( k1_tarski(B_82) = A_83
      | k1_xboole_0 = A_83
      | ~ r1_tarski(A_83,k1_tarski(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_472,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_70,c_462])).

tff(c_481,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_472])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_tarski(A_21),B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_703,plain,(
    ! [B_93] :
      ( r1_tarski('#skF_2',B_93)
      | ~ r2_hidden('#skF_1',B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_28])).

tff(c_759,plain,(
    ! [B_97] :
      ( r1_tarski('#skF_2',B_97)
      | r1_xboole_0(B_97,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_330,c_703])).

tff(c_8,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_765,plain,
    ( k1_xboole_0 = '#skF_3'
    | r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_759,c_8])).

tff(c_769,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_765])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_773,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_769,c_4])).

tff(c_490,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_46])).

tff(c_774,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_490])).

tff(c_776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.44  
% 2.64/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.44  
% 2.64/1.44  %Foreground sorts:
% 2.64/1.44  
% 2.64/1.44  
% 2.64/1.44  %Background operators:
% 2.64/1.44  
% 2.64/1.44  
% 2.64/1.44  %Foreground operators:
% 2.64/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.64/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.64/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.44  
% 2.64/1.45  tff(f_101, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.64/1.45  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.64/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.64/1.45  tff(f_61, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.64/1.45  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.64/1.45  tff(f_86, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.64/1.45  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.64/1.45  tff(f_45, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.64/1.45  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.64/1.45  tff(c_44, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.64/1.45  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.64/1.45  tff(c_124, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.45  tff(c_131, plain, (![B_46, A_45]: (r1_xboole_0(B_46, k1_tarski(A_45)) | r2_hidden(A_45, B_46))), inference(resolution, [status(thm)], [c_124, c_2])).
% 2.64/1.45  tff(c_46, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.64/1.45  tff(c_299, plain, (![A_67, C_68, B_69]: (r1_xboole_0(A_67, C_68) | ~r1_xboole_0(A_67, k2_xboole_0(B_69, C_68)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.64/1.45  tff(c_321, plain, (![A_72]: (r1_xboole_0(A_72, '#skF_3') | ~r1_xboole_0(A_72, k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_299])).
% 2.64/1.45  tff(c_330, plain, (![B_46]: (r1_xboole_0(B_46, '#skF_3') | r2_hidden('#skF_1', B_46))), inference(resolution, [status(thm)], [c_131, c_321])).
% 2.64/1.45  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.64/1.45  tff(c_67, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.45  tff(c_70, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_67])).
% 2.64/1.45  tff(c_462, plain, (![B_82, A_83]: (k1_tarski(B_82)=A_83 | k1_xboole_0=A_83 | ~r1_tarski(A_83, k1_tarski(B_82)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.64/1.45  tff(c_472, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_70, c_462])).
% 2.64/1.45  tff(c_481, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_472])).
% 2.64/1.45  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(k1_tarski(A_21), B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.64/1.45  tff(c_703, plain, (![B_93]: (r1_tarski('#skF_2', B_93) | ~r2_hidden('#skF_1', B_93))), inference(superposition, [status(thm), theory('equality')], [c_481, c_28])).
% 2.64/1.45  tff(c_759, plain, (![B_97]: (r1_tarski('#skF_2', B_97) | r1_xboole_0(B_97, '#skF_3'))), inference(resolution, [status(thm)], [c_330, c_703])).
% 2.64/1.45  tff(c_8, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.45  tff(c_765, plain, (k1_xboole_0='#skF_3' | r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_759, c_8])).
% 2.64/1.45  tff(c_769, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_765])).
% 2.64/1.45  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.45  tff(c_773, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_769, c_4])).
% 2.64/1.45  tff(c_490, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_46])).
% 2.64/1.45  tff(c_774, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_773, c_490])).
% 2.64/1.45  tff(c_776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_774])).
% 2.64/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.45  
% 2.64/1.45  Inference rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Ref     : 0
% 2.64/1.45  #Sup     : 175
% 2.64/1.45  #Fact    : 0
% 2.64/1.45  #Define  : 0
% 2.64/1.45  #Split   : 0
% 2.64/1.45  #Chain   : 0
% 2.64/1.45  #Close   : 0
% 2.64/1.45  
% 2.64/1.45  Ordering : KBO
% 2.64/1.45  
% 2.64/1.45  Simplification rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Subsume      : 8
% 2.64/1.45  #Demod        : 82
% 2.64/1.45  #Tautology    : 110
% 2.64/1.45  #SimpNegUnit  : 3
% 2.64/1.45  #BackRed      : 8
% 2.64/1.45  
% 2.64/1.45  #Partial instantiations: 0
% 2.64/1.45  #Strategies tried      : 1
% 2.64/1.45  
% 2.64/1.45  Timing (in seconds)
% 2.64/1.45  ----------------------
% 2.64/1.45  Preprocessing        : 0.34
% 2.64/1.45  Parsing              : 0.18
% 2.64/1.45  CNF conversion       : 0.02
% 2.64/1.45  Main loop            : 0.31
% 2.64/1.45  Inferencing          : 0.12
% 2.64/1.45  Reduction            : 0.10
% 2.64/1.45  Demodulation         : 0.08
% 2.64/1.45  BG Simplification    : 0.02
% 2.64/1.45  Subsumption          : 0.05
% 2.64/1.45  Abstraction          : 0.01
% 2.91/1.46  MUC search           : 0.00
% 2.91/1.46  Cooper               : 0.00
% 2.91/1.46  Total                : 0.68
% 2.91/1.46  Index Insertion      : 0.00
% 2.91/1.46  Index Deletion       : 0.00
% 2.91/1.46  Index Matching       : 0.00
% 2.91/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
