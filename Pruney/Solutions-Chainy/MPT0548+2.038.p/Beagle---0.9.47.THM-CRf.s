%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  84 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_18,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_10,C_45] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_73,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_68])).

tff(c_82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_101,plain,(
    ! [A_51] :
      ( k9_relat_1(A_51,k1_relat_1(A_51)) = k2_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_110,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_101])).

tff(c_114,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_24,c_110])).

tff(c_46,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_11] : r1_xboole_0(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [A_49,B_50] :
      ( ~ r1_xboole_0(A_49,B_50)
      | k3_xboole_0(A_49,B_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_98,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_91])).

tff(c_159,plain,(
    ! [B_55,A_56] :
      ( k9_relat_1(B_55,k3_xboole_0(k1_relat_1(B_55),A_56)) = k9_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_172,plain,(
    ! [A_56] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_56)) = k9_relat_1(k1_xboole_0,A_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_159])).

tff(c_177,plain,(
    ! [A_56] : k9_relat_1(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_114,c_98,c_172])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.22  
% 1.83/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.95/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.95/1.23  
% 1.98/1.24  tff(f_65, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.98/1.24  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.98/1.24  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.98/1.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.98/1.24  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.98/1.24  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.98/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.98/1.24  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.98/1.24  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 1.98/1.24  tff(f_79, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.98/1.24  tff(c_18, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.24  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.98/1.24  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.98/1.24  tff(c_57, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.24  tff(c_68, plain, (![A_10, C_45]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 1.98/1.24  tff(c_73, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_68])).
% 1.98/1.24  tff(c_82, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_73])).
% 1.98/1.24  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.98/1.24  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.98/1.24  tff(c_101, plain, (![A_51]: (k9_relat_1(A_51, k1_relat_1(A_51))=k2_relat_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.98/1.24  tff(c_110, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_101])).
% 1.98/1.24  tff(c_114, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_82, c_24, c_110])).
% 1.98/1.24  tff(c_46, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.24  tff(c_49, plain, (![A_11]: (r1_xboole_0(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_12, c_46])).
% 1.98/1.24  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.24  tff(c_91, plain, (![A_49, B_50]: (~r1_xboole_0(A_49, B_50) | k3_xboole_0(A_49, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_57])).
% 1.98/1.24  tff(c_98, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_49, c_91])).
% 1.98/1.24  tff(c_159, plain, (![B_55, A_56]: (k9_relat_1(B_55, k3_xboole_0(k1_relat_1(B_55), A_56))=k9_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.98/1.24  tff(c_172, plain, (![A_56]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_56))=k9_relat_1(k1_xboole_0, A_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_159])).
% 1.98/1.24  tff(c_177, plain, (![A_56]: (k9_relat_1(k1_xboole_0, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_114, c_98, c_172])).
% 1.98/1.24  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.98/1.24  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_28])).
% 1.98/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  Inference rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Ref     : 0
% 1.98/1.24  #Sup     : 34
% 1.98/1.24  #Fact    : 0
% 1.98/1.24  #Define  : 0
% 1.98/1.24  #Split   : 0
% 1.98/1.24  #Chain   : 0
% 1.98/1.24  #Close   : 0
% 1.98/1.24  
% 1.98/1.24  Ordering : KBO
% 1.98/1.24  
% 1.98/1.24  Simplification rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Subsume      : 1
% 1.98/1.24  #Demod        : 17
% 1.98/1.24  #Tautology    : 26
% 1.98/1.24  #SimpNegUnit  : 2
% 1.98/1.24  #BackRed      : 1
% 1.98/1.24  
% 1.98/1.24  #Partial instantiations: 0
% 1.98/1.24  #Strategies tried      : 1
% 1.98/1.24  
% 1.98/1.24  Timing (in seconds)
% 1.98/1.24  ----------------------
% 1.98/1.24  Preprocessing        : 0.29
% 1.98/1.24  Parsing              : 0.17
% 1.98/1.24  CNF conversion       : 0.02
% 1.98/1.24  Main loop            : 0.13
% 1.98/1.24  Inferencing          : 0.06
% 1.98/1.24  Reduction            : 0.04
% 1.98/1.24  Demodulation         : 0.03
% 1.98/1.24  BG Simplification    : 0.01
% 1.98/1.24  Subsumption          : 0.02
% 1.98/1.24  Abstraction          : 0.01
% 1.98/1.24  MUC search           : 0.00
% 1.98/1.24  Cooper               : 0.00
% 1.98/1.24  Total                : 0.44
% 1.98/1.24  Index Insertion      : 0.00
% 1.98/1.24  Index Deletion       : 0.00
% 1.98/1.24  Index Matching       : 0.00
% 1.98/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
