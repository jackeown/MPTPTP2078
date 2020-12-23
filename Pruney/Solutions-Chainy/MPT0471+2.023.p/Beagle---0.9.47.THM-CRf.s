%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:23 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   57 (  58 expanded)
%              Number of leaves         :   38 (  39 expanded)
%              Depth                    :    5
%              Number of atoms          :   38 (  40 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_46,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_44,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_1'(A_39),A_39)
      | v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [B_73,A_74] :
      ( ~ r2_hidden(B_73,A_74)
      | k4_xboole_0(A_74,k1_tarski(B_73)) != A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_175,plain,(
    ! [B_75] : ~ r2_hidden(B_75,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_169])).

tff(c_180,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_175])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [A_70] : k3_tarski(k1_tarski(A_70)) = k2_xboole_0(A_70,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_120])).

tff(c_22,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_36] : k3_tarski(k1_zfmisc_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    k3_tarski(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_28])).

tff(c_141,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_72])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_231,plain,(
    ! [A_81] :
      ( k2_xboole_0(k1_relat_1(A_81),k2_relat_1(A_81)) = k3_relat_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_240,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_231])).

tff(c_247,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_141,c_42,c_240])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.21  
% 2.12/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.22  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.12/1.22  
% 2.12/1.22  %Foreground sorts:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Background operators:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Foreground operators:
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.12/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.12/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.22  
% 2.12/1.23  tff(f_74, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 2.12/1.23  tff(f_65, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.12/1.23  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.12/1.23  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.12/1.23  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.23  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.12/1.23  tff(f_46, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.12/1.23  tff(f_53, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.12/1.23  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.23  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.12/1.23  tff(c_44, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.23  tff(c_36, plain, (![A_39]: (r2_hidden('#skF_1'(A_39), A_39) | v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.23  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.23  tff(c_169, plain, (![B_73, A_74]: (~r2_hidden(B_73, A_74) | k4_xboole_0(A_74, k1_tarski(B_73))!=A_74)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.23  tff(c_175, plain, (![B_75]: (~r2_hidden(B_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_169])).
% 2.12/1.23  tff(c_180, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_175])).
% 2.12/1.23  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.23  tff(c_120, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.23  tff(c_132, plain, (![A_70]: (k3_tarski(k1_tarski(A_70))=k2_xboole_0(A_70, A_70))), inference(superposition, [status(thm), theory('equality')], [c_6, c_120])).
% 2.12/1.23  tff(c_22, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.23  tff(c_28, plain, (![A_36]: (k3_tarski(k1_zfmisc_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.23  tff(c_72, plain, (k3_tarski(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_28])).
% 2.12/1.23  tff(c_141, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_132, c_72])).
% 2.12/1.23  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.23  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.23  tff(c_231, plain, (![A_81]: (k2_xboole_0(k1_relat_1(A_81), k2_relat_1(A_81))=k3_relat_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.12/1.23  tff(c_240, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_231])).
% 2.12/1.23  tff(c_247, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_180, c_141, c_42, c_240])).
% 2.12/1.23  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_247])).
% 2.12/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.23  
% 2.12/1.23  Inference rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Ref     : 0
% 2.12/1.23  #Sup     : 52
% 2.12/1.23  #Fact    : 0
% 2.12/1.23  #Define  : 0
% 2.12/1.23  #Split   : 0
% 2.12/1.23  #Chain   : 0
% 2.12/1.23  #Close   : 0
% 2.12/1.23  
% 2.12/1.23  Ordering : KBO
% 2.12/1.23  
% 2.12/1.23  Simplification rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Subsume      : 0
% 2.12/1.23  #Demod        : 5
% 2.12/1.23  #Tautology    : 43
% 2.12/1.23  #SimpNegUnit  : 3
% 2.12/1.23  #BackRed      : 0
% 2.12/1.23  
% 2.12/1.23  #Partial instantiations: 0
% 2.12/1.23  #Strategies tried      : 1
% 2.12/1.23  
% 2.12/1.23  Timing (in seconds)
% 2.12/1.23  ----------------------
% 2.12/1.23  Preprocessing        : 0.33
% 2.12/1.23  Parsing              : 0.18
% 2.12/1.23  CNF conversion       : 0.02
% 2.12/1.23  Main loop            : 0.15
% 2.12/1.23  Inferencing          : 0.06
% 2.12/1.23  Reduction            : 0.05
% 2.12/1.23  Demodulation         : 0.04
% 2.12/1.23  BG Simplification    : 0.01
% 2.12/1.23  Subsumption          : 0.01
% 2.12/1.23  Abstraction          : 0.01
% 2.12/1.23  MUC search           : 0.00
% 2.12/1.23  Cooper               : 0.00
% 2.12/1.23  Total                : 0.51
% 2.12/1.23  Index Insertion      : 0.00
% 2.12/1.23  Index Deletion       : 0.00
% 2.12/1.23  Index Matching       : 0.00
% 2.12/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
