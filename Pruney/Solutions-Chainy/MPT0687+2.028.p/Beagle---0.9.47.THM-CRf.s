%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 100 expanded)
%              Number of equality atoms :   35 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_177,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_34])).

tff(c_59,plain,(
    ! [A_23] :
      ( k10_relat_1(A_23,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,k1_tarski(B_12)) = A_11
      | r2_hidden(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_124,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_tarski(B_12))
      | r2_hidden(B_12,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_148,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,k1_tarski(B_12)) = k1_xboole_0
      | r2_hidden(B_12,A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_139])).

tff(c_239,plain,(
    ! [B_44,A_45] :
      ( k10_relat_1(B_44,k3_xboole_0(k2_relat_1(B_44),A_45)) = k10_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_506,plain,(
    ! [B_58,B_59] :
      ( k10_relat_1(B_58,k1_tarski(B_59)) = k10_relat_1(B_58,k1_xboole_0)
      | ~ v1_relat_1(B_58)
      | r2_hidden(B_59,k2_relat_1(B_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_239])).

tff(c_512,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k10_relat_1('#skF_2',k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_506,c_85])).

tff(c_516,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_63,c_512])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_516])).

tff(c_519,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_520,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_44,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),B_20) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ! [A_19] : k1_tarski(A_19) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_735,plain,(
    ! [B_81,A_82] :
      ( k10_relat_1(B_81,A_82) != k1_xboole_0
      | ~ r1_tarski(A_82,k2_relat_1(B_81))
      | k1_xboole_0 = A_82
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_739,plain,(
    ! [B_81,A_7] :
      ( k10_relat_1(B_81,k1_tarski(A_7)) != k1_xboole_0
      | k1_tarski(A_7) = k1_xboole_0
      | ~ v1_relat_1(B_81)
      | ~ r2_hidden(A_7,k2_relat_1(B_81)) ) ),
    inference(resolution,[status(thm)],[c_12,c_735])).

tff(c_914,plain,(
    ! [B_87,A_88] :
      ( k10_relat_1(B_87,k1_tarski(A_88)) != k1_xboole_0
      | ~ v1_relat_1(B_87)
      | ~ r2_hidden(A_88,k2_relat_1(B_87)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_739])).

tff(c_917,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_520,c_914])).

tff(c_921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_519,c_917])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.47  
% 2.86/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.47  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.86/1.47  
% 2.86/1.47  %Foreground sorts:
% 2.86/1.47  
% 2.86/1.47  
% 2.86/1.47  %Background operators:
% 2.86/1.47  
% 2.86/1.47  
% 2.86/1.47  %Foreground operators:
% 2.86/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.86/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.47  
% 2.86/1.48  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.86/1.48  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.86/1.48  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.86/1.48  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.86/1.48  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.86/1.48  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.86/1.48  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.86/1.48  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.86/1.48  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.86/1.48  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.86/1.48  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.48  tff(c_28, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.48  tff(c_85, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.86/1.48  tff(c_34, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.48  tff(c_177, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_85, c_34])).
% 2.86/1.48  tff(c_59, plain, (![A_23]: (k10_relat_1(A_23, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.86/1.48  tff(c_63, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_59])).
% 2.86/1.48  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.48  tff(c_68, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.48  tff(c_75, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 2.86/1.48  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k1_tarski(B_12))=A_11 | r2_hidden(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.48  tff(c_124, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.48  tff(c_139, plain, (![A_11, B_12]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_tarski(B_12)) | r2_hidden(B_12, A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_124])).
% 2.86/1.48  tff(c_148, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k1_tarski(B_12))=k1_xboole_0 | r2_hidden(B_12, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_139])).
% 2.86/1.48  tff(c_239, plain, (![B_44, A_45]: (k10_relat_1(B_44, k3_xboole_0(k2_relat_1(B_44), A_45))=k10_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.48  tff(c_506, plain, (![B_58, B_59]: (k10_relat_1(B_58, k1_tarski(B_59))=k10_relat_1(B_58, k1_xboole_0) | ~v1_relat_1(B_58) | r2_hidden(B_59, k2_relat_1(B_58)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_239])).
% 2.86/1.48  tff(c_512, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k10_relat_1('#skF_2', k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_506, c_85])).
% 2.86/1.48  tff(c_516, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_63, c_512])).
% 2.86/1.48  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_516])).
% 2.86/1.48  tff(c_519, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.86/1.48  tff(c_520, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_28])).
% 2.86/1.48  tff(c_44, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.48  tff(c_48, plain, (![A_19]: (k1_tarski(A_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_44])).
% 2.86/1.48  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.48  tff(c_735, plain, (![B_81, A_82]: (k10_relat_1(B_81, A_82)!=k1_xboole_0 | ~r1_tarski(A_82, k2_relat_1(B_81)) | k1_xboole_0=A_82 | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.86/1.48  tff(c_739, plain, (![B_81, A_7]: (k10_relat_1(B_81, k1_tarski(A_7))!=k1_xboole_0 | k1_tarski(A_7)=k1_xboole_0 | ~v1_relat_1(B_81) | ~r2_hidden(A_7, k2_relat_1(B_81)))), inference(resolution, [status(thm)], [c_12, c_735])).
% 2.86/1.48  tff(c_914, plain, (![B_87, A_88]: (k10_relat_1(B_87, k1_tarski(A_88))!=k1_xboole_0 | ~v1_relat_1(B_87) | ~r2_hidden(A_88, k2_relat_1(B_87)))), inference(negUnitSimplification, [status(thm)], [c_48, c_739])).
% 2.86/1.48  tff(c_917, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_520, c_914])).
% 2.86/1.48  tff(c_921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_519, c_917])).
% 2.86/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.48  
% 2.86/1.48  Inference rules
% 2.86/1.48  ----------------------
% 2.86/1.48  #Ref     : 0
% 2.86/1.48  #Sup     : 213
% 2.86/1.48  #Fact    : 0
% 2.86/1.48  #Define  : 0
% 2.86/1.48  #Split   : 1
% 2.86/1.48  #Chain   : 0
% 2.86/1.48  #Close   : 0
% 2.86/1.48  
% 2.86/1.48  Ordering : KBO
% 2.86/1.48  
% 2.86/1.48  Simplification rules
% 2.86/1.48  ----------------------
% 2.86/1.48  #Subsume      : 13
% 2.86/1.48  #Demod        : 105
% 2.86/1.48  #Tautology    : 138
% 2.86/1.48  #SimpNegUnit  : 8
% 2.86/1.48  #BackRed      : 0
% 2.86/1.48  
% 2.86/1.48  #Partial instantiations: 0
% 2.86/1.48  #Strategies tried      : 1
% 2.86/1.48  
% 2.86/1.48  Timing (in seconds)
% 2.86/1.48  ----------------------
% 2.86/1.49  Preprocessing        : 0.31
% 2.86/1.49  Parsing              : 0.17
% 2.86/1.49  CNF conversion       : 0.02
% 2.86/1.49  Main loop            : 0.36
% 2.86/1.49  Inferencing          : 0.15
% 2.86/1.49  Reduction            : 0.13
% 2.86/1.49  Demodulation         : 0.09
% 2.86/1.49  BG Simplification    : 0.02
% 2.86/1.49  Subsumption          : 0.05
% 2.86/1.49  Abstraction          : 0.02
% 2.86/1.49  MUC search           : 0.00
% 2.86/1.49  Cooper               : 0.00
% 2.86/1.49  Total                : 0.70
% 2.86/1.49  Index Insertion      : 0.00
% 2.86/1.49  Index Deletion       : 0.00
% 2.86/1.49  Index Matching       : 0.00
% 2.86/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
