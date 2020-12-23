%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  65 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 (  86 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_66,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_64,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_5'(A_54,B_55),A_54)
      | k1_xboole_0 = A_54
      | k1_tarski(B_55) = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_978,plain,(
    ! [D_112,A_113,B_114] :
      ( r2_hidden(D_112,k4_xboole_0(A_113,B_114))
      | r2_hidden(D_112,B_114)
      | ~ r2_hidden(D_112,A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1063,plain,(
    ! [D_117] :
      ( r2_hidden(D_117,k1_xboole_0)
      | r2_hidden(D_117,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_117,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_978])).

tff(c_34,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1083,plain,(
    ! [D_122] :
      ( D_122 = '#skF_7'
      | r2_hidden(D_122,k1_xboole_0)
      | ~ r2_hidden(D_122,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1063,c_34])).

tff(c_26,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_274,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_291,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_274])).

tff(c_295,plain,(
    ! [A_82] : k4_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_291])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_301,plain,(
    ! [D_8,A_82] :
      ( ~ r2_hidden(D_8,k1_xboole_0)
      | ~ r2_hidden(D_8,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_6])).

tff(c_1151,plain,(
    ! [D_124,A_125] :
      ( ~ r2_hidden(D_124,A_125)
      | D_124 = '#skF_7'
      | ~ r2_hidden(D_124,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1083,c_301])).

tff(c_1167,plain,(
    ! [C_126] :
      ( C_126 = '#skF_7'
      | ~ r2_hidden(C_126,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_1151])).

tff(c_1171,plain,(
    ! [B_55] :
      ( '#skF_5'('#skF_6',B_55) = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_tarski(B_55) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_64,c_1167])).

tff(c_1175,plain,(
    ! [B_127] :
      ( '#skF_5'('#skF_6',B_127) = '#skF_7'
      | k1_tarski(B_127) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1171])).

tff(c_1205,plain,(
    '#skF_5'('#skF_6','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_66])).

tff(c_62,plain,(
    ! [A_54,B_55] :
      ( '#skF_5'(A_54,B_55) != B_55
      | k1_xboole_0 = A_54
      | k1_tarski(B_55) = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1212,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_62])).

tff(c_1219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_68,c_1212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.55  
% 3.12/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.56  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 3.12/1.56  
% 3.12/1.56  %Foreground sorts:
% 3.12/1.56  
% 3.12/1.56  
% 3.12/1.56  %Background operators:
% 3.12/1.56  
% 3.12/1.56  
% 3.12/1.56  %Foreground operators:
% 3.12/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.12/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.12/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.12/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.12/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.12/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.12/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.12/1.56  
% 3.12/1.57  tff(f_96, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.12/1.57  tff(f_86, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.12/1.57  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.12/1.57  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.12/1.57  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.12/1.57  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.12/1.57  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.12/1.57  tff(c_66, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.57  tff(c_68, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.57  tff(c_64, plain, (![A_54, B_55]: (r2_hidden('#skF_5'(A_54, B_55), A_54) | k1_xboole_0=A_54 | k1_tarski(B_55)=A_54)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.12/1.57  tff(c_36, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.12/1.57  tff(c_70, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.57  tff(c_978, plain, (![D_112, A_113, B_114]: (r2_hidden(D_112, k4_xboole_0(A_113, B_114)) | r2_hidden(D_112, B_114) | ~r2_hidden(D_112, A_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.57  tff(c_1063, plain, (![D_117]: (r2_hidden(D_117, k1_xboole_0) | r2_hidden(D_117, k1_tarski('#skF_7')) | ~r2_hidden(D_117, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_978])).
% 3.12/1.57  tff(c_34, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.12/1.57  tff(c_1083, plain, (![D_122]: (D_122='#skF_7' | r2_hidden(D_122, k1_xboole_0) | ~r2_hidden(D_122, '#skF_6'))), inference(resolution, [status(thm)], [c_1063, c_34])).
% 3.12/1.57  tff(c_26, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.12/1.57  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.57  tff(c_274, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.57  tff(c_291, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_274])).
% 3.12/1.57  tff(c_295, plain, (![A_82]: (k4_xboole_0(A_82, k1_xboole_0)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_291])).
% 3.12/1.57  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.57  tff(c_301, plain, (![D_8, A_82]: (~r2_hidden(D_8, k1_xboole_0) | ~r2_hidden(D_8, A_82))), inference(superposition, [status(thm), theory('equality')], [c_295, c_6])).
% 3.12/1.57  tff(c_1151, plain, (![D_124, A_125]: (~r2_hidden(D_124, A_125) | D_124='#skF_7' | ~r2_hidden(D_124, '#skF_6'))), inference(resolution, [status(thm)], [c_1083, c_301])).
% 3.12/1.57  tff(c_1167, plain, (![C_126]: (C_126='#skF_7' | ~r2_hidden(C_126, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_1151])).
% 3.12/1.57  tff(c_1171, plain, (![B_55]: ('#skF_5'('#skF_6', B_55)='#skF_7' | k1_xboole_0='#skF_6' | k1_tarski(B_55)='#skF_6')), inference(resolution, [status(thm)], [c_64, c_1167])).
% 3.12/1.57  tff(c_1175, plain, (![B_127]: ('#skF_5'('#skF_6', B_127)='#skF_7' | k1_tarski(B_127)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_1171])).
% 3.12/1.57  tff(c_1205, plain, ('#skF_5'('#skF_6', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1175, c_66])).
% 3.12/1.57  tff(c_62, plain, (![A_54, B_55]: ('#skF_5'(A_54, B_55)!=B_55 | k1_xboole_0=A_54 | k1_tarski(B_55)=A_54)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.12/1.57  tff(c_1212, plain, (k1_xboole_0='#skF_6' | k1_tarski('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1205, c_62])).
% 3.12/1.57  tff(c_1219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_68, c_1212])).
% 3.12/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.57  
% 3.12/1.57  Inference rules
% 3.12/1.57  ----------------------
% 3.12/1.57  #Ref     : 0
% 3.12/1.57  #Sup     : 283
% 3.12/1.57  #Fact    : 0
% 3.12/1.57  #Define  : 0
% 3.12/1.57  #Split   : 0
% 3.12/1.57  #Chain   : 0
% 3.12/1.57  #Close   : 0
% 3.12/1.57  
% 3.12/1.57  Ordering : KBO
% 3.12/1.57  
% 3.12/1.57  Simplification rules
% 3.12/1.57  ----------------------
% 3.12/1.57  #Subsume      : 13
% 3.12/1.57  #Demod        : 119
% 3.12/1.57  #Tautology    : 173
% 3.12/1.57  #SimpNegUnit  : 3
% 3.12/1.57  #BackRed      : 1
% 3.12/1.57  
% 3.12/1.57  #Partial instantiations: 0
% 3.12/1.57  #Strategies tried      : 1
% 3.12/1.57  
% 3.12/1.57  Timing (in seconds)
% 3.12/1.57  ----------------------
% 3.12/1.57  Preprocessing        : 0.43
% 3.12/1.57  Parsing              : 0.24
% 3.12/1.57  CNF conversion       : 0.03
% 3.12/1.57  Main loop            : 0.38
% 3.12/1.57  Inferencing          : 0.13
% 3.12/1.57  Reduction            : 0.15
% 3.12/1.57  Demodulation         : 0.12
% 3.12/1.57  BG Simplification    : 0.03
% 3.12/1.57  Subsumption          : 0.06
% 3.12/1.57  Abstraction          : 0.02
% 3.12/1.57  MUC search           : 0.00
% 3.12/1.57  Cooper               : 0.00
% 3.12/1.57  Total                : 0.83
% 3.12/1.57  Index Insertion      : 0.00
% 3.12/1.57  Index Deletion       : 0.00
% 3.12/1.57  Index Matching       : 0.00
% 3.12/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
