%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:24 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   55 (  58 expanded)
%              Number of leaves         :   31 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  65 expanded)
%              Number of equality atoms :   38 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_89,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(k1_tarski(A_10),k1_tarski(B_11))
      | B_11 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_252,plain,(
    ! [A_70] :
      ( k2_xboole_0(k1_relat_1(A_70),k2_relat_1(A_70)) = k3_relat_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_261,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_252])).

tff(c_267,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38,c_261])).

tff(c_268,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_267])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [C_45,B_46] : k4_xboole_0(k1_tarski(C_45),k2_tarski(B_46,C_45)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,(
    ! [A_9] : k4_xboole_0(k1_tarski(A_9),k1_tarski(A_9)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_85])).

tff(c_193,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),k1_tarski(B_64)) = k1_tarski(A_63)
      | B_64 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_199,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),k1_tarski(A_63)) = k3_xboole_0(k1_tarski(A_63),k1_tarski(B_64))
      | B_64 = A_63 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_8])).

tff(c_235,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(k1_tarski(A_67),k1_tarski(B_68)) = k1_xboole_0
      | B_68 = A_67 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_199])).

tff(c_32,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_139,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(A_55,B_56)
      | v1_relat_1(k3_xboole_0(A_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_32,c_139])).

tff(c_241,plain,(
    ! [A_67,B_68] :
      ( ~ r1_xboole_0(k1_tarski(A_67),k1_tarski(B_68))
      | v1_relat_1(k1_xboole_0)
      | B_68 = A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_144])).

tff(c_329,plain,(
    ! [A_79,B_80] :
      ( ~ r1_xboole_0(k1_tarski(A_79),k1_tarski(B_80))
      | B_80 = A_79 ) ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_241])).

tff(c_334,plain,(
    ! [B_81,A_82] : B_81 = A_82 ),
    inference(resolution,[status(thm)],[c_12,c_329])).

tff(c_1246,plain,(
    ! [A_82] : k1_xboole_0 != A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_40])).

tff(c_1258,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.37  
% 2.59/1.37  %Foreground sorts:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Background operators:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Foreground operators:
% 2.59/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.37  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.59/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.59/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.59/1.37  
% 2.59/1.38  tff(f_50, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.59/1.38  tff(f_89, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 2.59/1.38  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.59/1.38  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.59/1.38  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.59/1.38  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.59/1.38  tff(f_70, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 2.59/1.38  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.59/1.38  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.59/1.38  tff(f_80, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.59/1.38  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.59/1.38  tff(c_12, plain, (![A_10, B_11]: (r1_xboole_0(k1_tarski(A_10), k1_tarski(B_11)) | B_11=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.38  tff(c_40, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.59/1.38  tff(c_6, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.38  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.59/1.38  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.59/1.38  tff(c_252, plain, (![A_70]: (k2_xboole_0(k1_relat_1(A_70), k2_relat_1(A_70))=k3_relat_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.59/1.38  tff(c_261, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_252])).
% 2.59/1.38  tff(c_267, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_38, c_261])).
% 2.59/1.38  tff(c_268, plain, (~v1_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_40, c_267])).
% 2.59/1.38  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.38  tff(c_85, plain, (![C_45, B_46]: (k4_xboole_0(k1_tarski(C_45), k2_tarski(B_46, C_45))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.38  tff(c_92, plain, (![A_9]: (k4_xboole_0(k1_tarski(A_9), k1_tarski(A_9))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_85])).
% 2.59/1.38  tff(c_193, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), k1_tarski(B_64))=k1_tarski(A_63) | B_64=A_63)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.59/1.38  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.38  tff(c_199, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), k1_tarski(A_63))=k3_xboole_0(k1_tarski(A_63), k1_tarski(B_64)) | B_64=A_63)), inference(superposition, [status(thm), theory('equality')], [c_193, c_8])).
% 2.59/1.38  tff(c_235, plain, (![A_67, B_68]: (k3_xboole_0(k1_tarski(A_67), k1_tarski(B_68))=k1_xboole_0 | B_68=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_199])).
% 2.59/1.38  tff(c_32, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.38  tff(c_139, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.38  tff(c_144, plain, (![A_55, B_56]: (~r1_xboole_0(A_55, B_56) | v1_relat_1(k3_xboole_0(A_55, B_56)))), inference(resolution, [status(thm)], [c_32, c_139])).
% 2.59/1.38  tff(c_241, plain, (![A_67, B_68]: (~r1_xboole_0(k1_tarski(A_67), k1_tarski(B_68)) | v1_relat_1(k1_xboole_0) | B_68=A_67)), inference(superposition, [status(thm), theory('equality')], [c_235, c_144])).
% 2.59/1.38  tff(c_329, plain, (![A_79, B_80]: (~r1_xboole_0(k1_tarski(A_79), k1_tarski(B_80)) | B_80=A_79)), inference(negUnitSimplification, [status(thm)], [c_268, c_241])).
% 2.59/1.38  tff(c_334, plain, (![B_81, A_82]: (B_81=A_82)), inference(resolution, [status(thm)], [c_12, c_329])).
% 2.59/1.38  tff(c_1246, plain, (![A_82]: (k1_xboole_0!=A_82)), inference(superposition, [status(thm), theory('equality')], [c_334, c_40])).
% 2.59/1.38  tff(c_1258, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1246])).
% 2.59/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.38  
% 2.59/1.38  Inference rules
% 2.59/1.38  ----------------------
% 2.59/1.38  #Ref     : 1
% 2.59/1.38  #Sup     : 294
% 2.59/1.38  #Fact    : 0
% 2.59/1.38  #Define  : 0
% 2.59/1.38  #Split   : 2
% 2.59/1.38  #Chain   : 0
% 2.59/1.38  #Close   : 0
% 2.59/1.38  
% 2.59/1.38  Ordering : KBO
% 2.59/1.38  
% 2.59/1.38  Simplification rules
% 2.59/1.38  ----------------------
% 2.59/1.38  #Subsume      : 27
% 2.59/1.38  #Demod        : 14
% 2.59/1.38  #Tautology    : 49
% 2.59/1.38  #SimpNegUnit  : 11
% 2.59/1.38  #BackRed      : 3
% 2.59/1.38  
% 2.59/1.38  #Partial instantiations: 392
% 2.59/1.38  #Strategies tried      : 1
% 2.59/1.38  
% 2.59/1.38  Timing (in seconds)
% 2.59/1.38  ----------------------
% 2.59/1.39  Preprocessing        : 0.30
% 2.59/1.39  Parsing              : 0.16
% 2.59/1.39  CNF conversion       : 0.02
% 2.59/1.39  Main loop            : 0.30
% 2.59/1.39  Inferencing          : 0.13
% 2.59/1.39  Reduction            : 0.09
% 2.59/1.39  Demodulation         : 0.06
% 2.59/1.39  BG Simplification    : 0.02
% 2.59/1.39  Subsumption          : 0.05
% 2.59/1.39  Abstraction          : 0.02
% 2.59/1.39  MUC search           : 0.00
% 2.59/1.39  Cooper               : 0.00
% 2.59/1.39  Total                : 0.63
% 2.59/1.39  Index Insertion      : 0.00
% 2.59/1.39  Index Deletion       : 0.00
% 2.59/1.39  Index Matching       : 0.00
% 2.59/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
