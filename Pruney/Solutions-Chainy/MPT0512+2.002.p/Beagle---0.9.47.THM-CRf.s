%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:57 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  61 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(c_44,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k2_xboole_0(A_56,B_57)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_143,plain,(
    ! [A_75,B_76,C_77] : k4_xboole_0(k3_xboole_0(A_75,B_76),k3_xboole_0(A_75,C_77)) = k3_xboole_0(A_75,k4_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_75,C_77] : k3_xboole_0(A_75,k4_xboole_0(C_77,C_77)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_73])).

tff(c_165,plain,(
    ! [A_75] : k3_xboole_0(A_75,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_150])).

tff(c_359,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden('#skF_2'(A_111,B_112,C_113),A_111)
      | r2_hidden('#skF_4'(A_111,B_112,C_113),C_113)
      | k2_zfmisc_1(A_111,B_112) = C_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_38,plain,(
    ! [C_48,B_47] : ~ r2_hidden(C_48,k4_xboole_0(B_47,k1_tarski(C_48))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [C_48] : ~ r2_hidden(C_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_38])).

tff(c_829,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_2'(A_151,B_152,k1_xboole_0),A_151)
      | k2_zfmisc_1(A_151,B_152) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_359,c_81])).

tff(c_922,plain,(
    ! [B_153] : k2_zfmisc_1(k1_xboole_0,B_153) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_829,c_81])).

tff(c_42,plain,(
    ! [B_50,A_49] :
      ( k3_xboole_0(B_50,k2_zfmisc_1(A_49,k2_relat_1(B_50))) = k7_relat_1(B_50,A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_973,plain,(
    ! [B_50] :
      ( k7_relat_1(B_50,k1_xboole_0) = k3_xboole_0(B_50,k1_xboole_0)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_42])).

tff(c_1055,plain,(
    ! [B_156] :
      ( k7_relat_1(B_156,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_973])).

tff(c_1058,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1055])).

tff(c_1062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_3
% 2.67/1.42  
% 2.67/1.42  %Foreground sorts:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Background operators:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Foreground operators:
% 2.67/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.67/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.67/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.67/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.67/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.67/1.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.67/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.42  
% 2.67/1.43  tff(f_63, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 2.67/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.67/1.43  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.67/1.43  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 2.67/1.43  tff(f_47, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.67/1.43  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.67/1.43  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 2.67/1.43  tff(c_44, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.43  tff(c_46, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.43  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.43  tff(c_66, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k2_xboole_0(A_56, B_57))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.43  tff(c_73, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 2.67/1.43  tff(c_143, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k3_xboole_0(A_75, B_76), k3_xboole_0(A_75, C_77))=k3_xboole_0(A_75, k4_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.43  tff(c_150, plain, (![A_75, C_77]: (k3_xboole_0(A_75, k4_xboole_0(C_77, C_77))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_143, c_73])).
% 2.67/1.43  tff(c_165, plain, (![A_75]: (k3_xboole_0(A_75, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_150])).
% 2.67/1.43  tff(c_359, plain, (![A_111, B_112, C_113]: (r2_hidden('#skF_2'(A_111, B_112, C_113), A_111) | r2_hidden('#skF_4'(A_111, B_112, C_113), C_113) | k2_zfmisc_1(A_111, B_112)=C_113)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.43  tff(c_76, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 2.67/1.43  tff(c_38, plain, (![C_48, B_47]: (~r2_hidden(C_48, k4_xboole_0(B_47, k1_tarski(C_48))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.43  tff(c_81, plain, (![C_48]: (~r2_hidden(C_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_76, c_38])).
% 2.67/1.43  tff(c_829, plain, (![A_151, B_152]: (r2_hidden('#skF_2'(A_151, B_152, k1_xboole_0), A_151) | k2_zfmisc_1(A_151, B_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_359, c_81])).
% 2.67/1.43  tff(c_922, plain, (![B_153]: (k2_zfmisc_1(k1_xboole_0, B_153)=k1_xboole_0)), inference(resolution, [status(thm)], [c_829, c_81])).
% 2.67/1.43  tff(c_42, plain, (![B_50, A_49]: (k3_xboole_0(B_50, k2_zfmisc_1(A_49, k2_relat_1(B_50)))=k7_relat_1(B_50, A_49) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.43  tff(c_973, plain, (![B_50]: (k7_relat_1(B_50, k1_xboole_0)=k3_xboole_0(B_50, k1_xboole_0) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_922, c_42])).
% 2.67/1.43  tff(c_1055, plain, (![B_156]: (k7_relat_1(B_156, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_973])).
% 2.67/1.43  tff(c_1058, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1055])).
% 2.67/1.43  tff(c_1062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1058])).
% 2.67/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.43  
% 2.67/1.43  Inference rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Ref     : 0
% 2.67/1.43  #Sup     : 212
% 2.67/1.43  #Fact    : 0
% 2.67/1.43  #Define  : 0
% 2.67/1.43  #Split   : 0
% 2.67/1.43  #Chain   : 0
% 2.67/1.43  #Close   : 0
% 2.67/1.43  
% 2.67/1.43  Ordering : KBO
% 2.67/1.43  
% 2.67/1.43  Simplification rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Subsume      : 51
% 2.67/1.43  #Demod        : 44
% 2.67/1.43  #Tautology    : 39
% 2.67/1.43  #SimpNegUnit  : 6
% 2.67/1.43  #BackRed      : 10
% 2.67/1.43  
% 2.67/1.43  #Partial instantiations: 0
% 2.67/1.43  #Strategies tried      : 1
% 2.67/1.43  
% 2.67/1.43  Timing (in seconds)
% 2.67/1.43  ----------------------
% 2.67/1.44  Preprocessing        : 0.33
% 2.67/1.44  Parsing              : 0.17
% 2.67/1.44  CNF conversion       : 0.03
% 2.67/1.44  Main loop            : 0.35
% 2.67/1.44  Inferencing          : 0.14
% 2.67/1.44  Reduction            : 0.10
% 2.67/1.44  Demodulation         : 0.06
% 2.67/1.44  BG Simplification    : 0.02
% 2.67/1.44  Subsumption          : 0.06
% 2.67/1.44  Abstraction          : 0.03
% 2.67/1.44  MUC search           : 0.00
% 2.67/1.44  Cooper               : 0.00
% 2.67/1.44  Total                : 0.71
% 2.67/1.44  Index Insertion      : 0.00
% 2.67/1.44  Index Deletion       : 0.00
% 2.67/1.44  Index Matching       : 0.00
% 2.67/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
