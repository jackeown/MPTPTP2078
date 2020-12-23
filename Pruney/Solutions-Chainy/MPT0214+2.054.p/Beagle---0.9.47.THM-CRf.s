%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:37 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   56 (  82 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 108 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [B_53,A_54] :
      ( ~ r2_hidden(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [C_18] : ~ v1_xboole_0(k1_tarski(C_18)) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_75,plain,(
    ! [A_58] :
      ( v1_xboole_0(A_58)
      | r2_hidden('#skF_1'(A_58),A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_79,plain,(
    ! [A_14] :
      ( '#skF_1'(k1_tarski(A_14)) = A_14
      | v1_xboole_0(k1_tarski(A_14)) ) ),
    inference(resolution,[status(thm)],[c_75,c_16])).

tff(c_85,plain,(
    ! [A_14] : '#skF_1'(k1_tarski(A_14)) = A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_79])).

tff(c_44,plain,(
    ! [B_48] : r1_tarski(k1_tarski(B_48),k1_tarski(B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_101,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_111,plain,(
    ! [B_48] : k3_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) = k1_tarski(B_48) ),
    inference(resolution,[status(thm)],[c_44,c_101])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_170,plain,(
    ! [A_73,B_74] :
      ( ~ r1_xboole_0(A_73,B_74)
      | v1_xboole_0(k3_xboole_0(A_73,B_74)) ) ),
    inference(resolution,[status(thm)],[c_4,c_149])).

tff(c_173,plain,(
    ! [B_48] :
      ( ~ r1_xboole_0(k1_tarski(B_48),k1_tarski(B_48))
      | v1_xboole_0(k1_tarski(B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_170])).

tff(c_182,plain,(
    ! [B_75] : ~ r1_xboole_0(k1_tarski(B_75),k1_tarski(B_75)) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_173])).

tff(c_185,plain,(
    ! [B_75] : k3_xboole_0(k1_tarski(B_75),k1_tarski(B_75)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_182])).

tff(c_187,plain,(
    ! [B_75] : k1_tarski(B_75) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_185])).

tff(c_50,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_208,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(B_81) = A_82
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_tarski(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_214,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_208])).

tff(c_224,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_214])).

tff(c_256,plain,(
    '#skF_1'(k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_85])).

tff(c_281,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_256])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:53:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.25  
% 2.27/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.27/1.25  
% 2.27/1.25  %Foreground sorts:
% 2.27/1.25  
% 2.27/1.25  
% 2.27/1.25  %Background operators:
% 2.27/1.25  
% 2.27/1.25  
% 2.27/1.25  %Foreground operators:
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.27/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.27/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.27/1.25  
% 2.27/1.26  tff(f_85, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.27/1.26  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.27/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.27/1.26  tff(f_80, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.27/1.26  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.27/1.26  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.27/1.26  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.27/1.26  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.26  tff(c_18, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.26  tff(c_63, plain, (![B_53, A_54]: (~r2_hidden(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.26  tff(c_67, plain, (![C_18]: (~v1_xboole_0(k1_tarski(C_18)))), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.27/1.26  tff(c_75, plain, (![A_58]: (v1_xboole_0(A_58) | r2_hidden('#skF_1'(A_58), A_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.26  tff(c_16, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.26  tff(c_79, plain, (![A_14]: ('#skF_1'(k1_tarski(A_14))=A_14 | v1_xboole_0(k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_75, c_16])).
% 2.27/1.26  tff(c_85, plain, (![A_14]: ('#skF_1'(k1_tarski(A_14))=A_14)), inference(negUnitSimplification, [status(thm)], [c_67, c_79])).
% 2.27/1.26  tff(c_44, plain, (![B_48]: (r1_tarski(k1_tarski(B_48), k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.27/1.26  tff(c_101, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.26  tff(c_111, plain, (![B_48]: (k3_xboole_0(k1_tarski(B_48), k1_tarski(B_48))=k1_tarski(B_48))), inference(resolution, [status(thm)], [c_44, c_101])).
% 2.27/1.26  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.26  tff(c_149, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.26  tff(c_170, plain, (![A_73, B_74]: (~r1_xboole_0(A_73, B_74) | v1_xboole_0(k3_xboole_0(A_73, B_74)))), inference(resolution, [status(thm)], [c_4, c_149])).
% 2.27/1.26  tff(c_173, plain, (![B_48]: (~r1_xboole_0(k1_tarski(B_48), k1_tarski(B_48)) | v1_xboole_0(k1_tarski(B_48)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_170])).
% 2.27/1.26  tff(c_182, plain, (![B_75]: (~r1_xboole_0(k1_tarski(B_75), k1_tarski(B_75)))), inference(negUnitSimplification, [status(thm)], [c_67, c_173])).
% 2.27/1.26  tff(c_185, plain, (![B_75]: (k3_xboole_0(k1_tarski(B_75), k1_tarski(B_75))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_182])).
% 2.27/1.26  tff(c_187, plain, (![B_75]: (k1_tarski(B_75)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_185])).
% 2.27/1.26  tff(c_50, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.26  tff(c_208, plain, (![B_81, A_82]: (k1_tarski(B_81)=A_82 | k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_tarski(B_81)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.27/1.26  tff(c_214, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_208])).
% 2.27/1.26  tff(c_224, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_187, c_214])).
% 2.27/1.26  tff(c_256, plain, ('#skF_1'(k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_224, c_85])).
% 2.27/1.26  tff(c_281, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_256])).
% 2.27/1.26  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_281])).
% 2.27/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.26  
% 2.27/1.26  Inference rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Ref     : 0
% 2.27/1.26  #Sup     : 52
% 2.27/1.26  #Fact    : 0
% 2.27/1.26  #Define  : 0
% 2.27/1.26  #Split   : 2
% 2.27/1.26  #Chain   : 0
% 2.27/1.26  #Close   : 0
% 2.27/1.26  
% 2.27/1.26  Ordering : KBO
% 2.27/1.26  
% 2.27/1.26  Simplification rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Subsume      : 7
% 2.27/1.26  #Demod        : 21
% 2.27/1.26  #Tautology    : 26
% 2.27/1.26  #SimpNegUnit  : 8
% 2.27/1.26  #BackRed      : 3
% 2.27/1.26  
% 2.27/1.26  #Partial instantiations: 0
% 2.27/1.26  #Strategies tried      : 1
% 2.27/1.26  
% 2.27/1.26  Timing (in seconds)
% 2.27/1.26  ----------------------
% 2.27/1.27  Preprocessing        : 0.33
% 2.27/1.27  Parsing              : 0.17
% 2.27/1.27  CNF conversion       : 0.02
% 2.27/1.27  Main loop            : 0.17
% 2.27/1.27  Inferencing          : 0.06
% 2.27/1.27  Reduction            : 0.06
% 2.27/1.27  Demodulation         : 0.04
% 2.27/1.27  BG Simplification    : 0.02
% 2.27/1.27  Subsumption          : 0.03
% 2.27/1.27  Abstraction          : 0.01
% 2.27/1.27  MUC search           : 0.00
% 2.27/1.27  Cooper               : 0.00
% 2.27/1.27  Total                : 0.53
% 2.27/1.27  Index Insertion      : 0.00
% 2.27/1.27  Index Deletion       : 0.00
% 2.27/1.27  Index Matching       : 0.00
% 2.27/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
