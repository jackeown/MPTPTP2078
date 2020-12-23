%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:29 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :   59 (  89 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 149 expanded)
%              Number of equality atoms :   45 ( 109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_66,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_386,plain,(
    ! [D_80,B_81,A_82] :
      ( ~ r2_hidden(D_80,B_81)
      | r2_hidden(D_80,k2_xboole_0(A_82,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_402,plain,(
    ! [D_83] :
      ( ~ r2_hidden(D_83,'#skF_8')
      | r2_hidden(D_83,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_386])).

tff(c_28,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_416,plain,(
    ! [D_87] :
      ( D_87 = '#skF_6'
      | ~ r2_hidden(D_87,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_402,c_28])).

tff(c_420,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_416])).

tff(c_423,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_420])).

tff(c_427,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_22])).

tff(c_430,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_427])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_91,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_91])).

tff(c_40,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3426,plain,(
    ! [B_3210,C_3211,A_3212] :
      ( k2_tarski(B_3210,C_3211) = A_3212
      | k1_tarski(C_3211) = A_3212
      | k1_tarski(B_3210) = A_3212
      | k1_xboole_0 = A_3212
      | ~ r1_tarski(A_3212,k2_tarski(B_3210,C_3211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3445,plain,(
    ! [A_18,A_3212] :
      ( k2_tarski(A_18,A_18) = A_3212
      | k1_tarski(A_18) = A_3212
      | k1_tarski(A_18) = A_3212
      | k1_xboole_0 = A_3212
      | ~ r1_tarski(A_3212,k1_tarski(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3426])).

tff(c_6961,plain,(
    ! [A_6643,A_6644] :
      ( k1_tarski(A_6643) = A_6644
      | k1_tarski(A_6643) = A_6644
      | k1_tarski(A_6643) = A_6644
      | k1_xboole_0 = A_6644
      | ~ r1_tarski(A_6644,k1_tarski(A_6643)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3445])).

tff(c_6979,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_94,c_6961])).

tff(c_6988,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6979])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_tarski(A_24),B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7780,plain,(
    ! [B_6938] :
      ( r1_tarski('#skF_7',B_6938)
      | ~ r2_hidden('#skF_6',B_6938) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6988,c_48])).

tff(c_7938,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_430,c_7780])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7955,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7938,c_24])).

tff(c_7007,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6988,c_68])).

tff(c_8044,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7955,c_7007])).

tff(c_8046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_8044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:35:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.63  
% 7.23/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.63  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 7.23/2.63  
% 7.23/2.63  %Foreground sorts:
% 7.23/2.63  
% 7.23/2.63  
% 7.23/2.63  %Background operators:
% 7.23/2.63  
% 7.23/2.63  
% 7.23/2.63  %Foreground operators:
% 7.23/2.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.23/2.63  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 7.23/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.23/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.23/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.23/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.23/2.63  tff('#skF_7', type, '#skF_7': $i).
% 7.23/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.23/2.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.23/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.23/2.63  tff('#skF_6', type, '#skF_6': $i).
% 7.23/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.23/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.23/2.63  tff('#skF_8', type, '#skF_8': $i).
% 7.23/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.23/2.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.23/2.63  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.23/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.23/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.23/2.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.23/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.23/2.63  
% 7.23/2.64  tff(f_96, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 7.23/2.64  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.23/2.64  tff(f_35, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 7.23/2.64  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.23/2.64  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.23/2.64  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.23/2.64  tff(f_81, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 7.23/2.64  tff(f_66, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.23/2.64  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.23/2.64  tff(c_66, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.23/2.64  tff(c_62, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.23/2.64  tff(c_22, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.23/2.64  tff(c_68, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.23/2.64  tff(c_386, plain, (![D_80, B_81, A_82]: (~r2_hidden(D_80, B_81) | r2_hidden(D_80, k2_xboole_0(A_82, B_81)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.23/2.64  tff(c_402, plain, (![D_83]: (~r2_hidden(D_83, '#skF_8') | r2_hidden(D_83, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_386])).
% 7.23/2.64  tff(c_28, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.23/2.64  tff(c_416, plain, (![D_87]: (D_87='#skF_6' | ~r2_hidden(D_87, '#skF_8'))), inference(resolution, [status(thm)], [c_402, c_28])).
% 7.23/2.64  tff(c_420, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_416])).
% 7.23/2.64  tff(c_423, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_62, c_420])).
% 7.23/2.64  tff(c_427, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_423, c_22])).
% 7.23/2.64  tff(c_430, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_427])).
% 7.23/2.64  tff(c_64, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.23/2.64  tff(c_91, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.23/2.64  tff(c_94, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_91])).
% 7.23/2.64  tff(c_40, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.23/2.64  tff(c_3426, plain, (![B_3210, C_3211, A_3212]: (k2_tarski(B_3210, C_3211)=A_3212 | k1_tarski(C_3211)=A_3212 | k1_tarski(B_3210)=A_3212 | k1_xboole_0=A_3212 | ~r1_tarski(A_3212, k2_tarski(B_3210, C_3211)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.23/2.64  tff(c_3445, plain, (![A_18, A_3212]: (k2_tarski(A_18, A_18)=A_3212 | k1_tarski(A_18)=A_3212 | k1_tarski(A_18)=A_3212 | k1_xboole_0=A_3212 | ~r1_tarski(A_3212, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3426])).
% 7.23/2.64  tff(c_6961, plain, (![A_6643, A_6644]: (k1_tarski(A_6643)=A_6644 | k1_tarski(A_6643)=A_6644 | k1_tarski(A_6643)=A_6644 | k1_xboole_0=A_6644 | ~r1_tarski(A_6644, k1_tarski(A_6643)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3445])).
% 7.23/2.64  tff(c_6979, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_94, c_6961])).
% 7.23/2.64  tff(c_6988, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_64, c_6979])).
% 7.23/2.64  tff(c_48, plain, (![A_24, B_25]: (r1_tarski(k1_tarski(A_24), B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.23/2.64  tff(c_7780, plain, (![B_6938]: (r1_tarski('#skF_7', B_6938) | ~r2_hidden('#skF_6', B_6938))), inference(superposition, [status(thm), theory('equality')], [c_6988, c_48])).
% 7.23/2.64  tff(c_7938, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_430, c_7780])).
% 7.23/2.64  tff(c_24, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.23/2.64  tff(c_7955, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_7938, c_24])).
% 7.23/2.64  tff(c_7007, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6988, c_68])).
% 7.23/2.64  tff(c_8044, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7955, c_7007])).
% 7.23/2.64  tff(c_8046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_8044])).
% 7.23/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.64  
% 7.23/2.64  Inference rules
% 7.23/2.64  ----------------------
% 7.23/2.64  #Ref     : 0
% 7.23/2.64  #Sup     : 2004
% 7.23/2.64  #Fact    : 8
% 7.23/2.64  #Define  : 0
% 7.23/2.64  #Split   : 12
% 7.23/2.64  #Chain   : 0
% 7.23/2.64  #Close   : 0
% 7.23/2.64  
% 7.23/2.64  Ordering : KBO
% 7.23/2.64  
% 7.23/2.64  Simplification rules
% 7.23/2.64  ----------------------
% 7.23/2.64  #Subsume      : 365
% 7.23/2.64  #Demod        : 650
% 7.23/2.64  #Tautology    : 439
% 7.23/2.64  #SimpNegUnit  : 73
% 7.23/2.64  #BackRed      : 29
% 7.23/2.64  
% 7.23/2.64  #Partial instantiations: 2558
% 7.23/2.64  #Strategies tried      : 1
% 7.23/2.64  
% 7.23/2.64  Timing (in seconds)
% 7.23/2.64  ----------------------
% 7.31/2.64  Preprocessing        : 0.33
% 7.31/2.64  Parsing              : 0.18
% 7.31/2.64  CNF conversion       : 0.02
% 7.31/2.64  Main loop            : 1.48
% 7.31/2.64  Inferencing          : 0.48
% 7.31/2.64  Reduction            : 0.49
% 7.31/2.64  Demodulation         : 0.37
% 7.31/2.64  BG Simplification    : 0.05
% 7.31/2.64  Subsumption          : 0.36
% 7.31/2.64  Abstraction          : 0.06
% 7.31/2.64  MUC search           : 0.00
% 7.31/2.64  Cooper               : 0.00
% 7.31/2.64  Total                : 1.84
% 7.31/2.64  Index Insertion      : 0.00
% 7.31/2.64  Index Deletion       : 0.00
% 7.31/2.64  Index Matching       : 0.00
% 7.31/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
