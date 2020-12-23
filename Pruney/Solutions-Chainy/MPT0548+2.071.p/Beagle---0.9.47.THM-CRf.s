%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:44 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  71 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_71,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_43,axiom,(
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

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_55,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_55])).

tff(c_68,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_24,c_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_75,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,(
    ! [A_13,C_30] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_75])).

tff(c_96,plain,(
    ! [C_31] : ~ r2_hidden(C_31,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_109,plain,(
    ! [B_2] : r1_xboole_0(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_122,plain,(
    ! [A_36,B_37] :
      ( ~ r1_xboole_0(A_36,B_37)
      | k3_xboole_0(A_36,B_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_129,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_122])).

tff(c_319,plain,(
    ! [B_53,A_54] :
      ( k9_relat_1(B_53,k3_xboole_0(k1_relat_1(B_53),A_54)) = k9_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_336,plain,(
    ! [A_54] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_54)) = k9_relat_1(k1_xboole_0,A_54)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_319])).

tff(c_341,plain,(
    ! [A_54] : k9_relat_1(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_68,c_129,c_336])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.89/1.22  
% 1.89/1.22  %Foreground sorts:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Background operators:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Foreground operators:
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.89/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.22  
% 1.89/1.23  tff(f_83, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.89/1.23  tff(f_71, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.89/1.23  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.89/1.23  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.89/1.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.89/1.23  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.89/1.23  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.89/1.23  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.89/1.23  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.89/1.23  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 1.89/1.23  tff(f_86, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.89/1.23  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.89/1.23  tff(c_44, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.23  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_44])).
% 1.89/1.23  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.89/1.23  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.89/1.23  tff(c_55, plain, (![A_23]: (k9_relat_1(A_23, k1_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.89/1.23  tff(c_64, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_55])).
% 1.89/1.23  tff(c_68, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_24, c_64])).
% 1.89/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.23  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.89/1.23  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.89/1.23  tff(c_75, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.23  tff(c_90, plain, (![A_13, C_30]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_75])).
% 1.89/1.23  tff(c_96, plain, (![C_31]: (~r2_hidden(C_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_90])).
% 1.89/1.23  tff(c_109, plain, (![B_2]: (r1_xboole_0(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_96])).
% 1.89/1.23  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.23  tff(c_122, plain, (![A_36, B_37]: (~r1_xboole_0(A_36, B_37) | k3_xboole_0(A_36, B_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_75])).
% 1.89/1.23  tff(c_129, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_122])).
% 1.89/1.23  tff(c_319, plain, (![B_53, A_54]: (k9_relat_1(B_53, k3_xboole_0(k1_relat_1(B_53), A_54))=k9_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.89/1.23  tff(c_336, plain, (![A_54]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_54))=k9_relat_1(k1_xboole_0, A_54) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_319])).
% 1.89/1.23  tff(c_341, plain, (![A_54]: (k9_relat_1(k1_xboole_0, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_68, c_129, c_336])).
% 1.89/1.23  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.89/1.23  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_30])).
% 1.89/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  Inference rules
% 1.89/1.23  ----------------------
% 1.89/1.23  #Ref     : 0
% 1.89/1.23  #Sup     : 74
% 1.89/1.23  #Fact    : 0
% 1.89/1.23  #Define  : 0
% 1.89/1.23  #Split   : 0
% 1.89/1.23  #Chain   : 0
% 1.89/1.23  #Close   : 0
% 1.89/1.23  
% 1.89/1.23  Ordering : KBO
% 1.89/1.23  
% 1.89/1.23  Simplification rules
% 1.89/1.23  ----------------------
% 1.89/1.23  #Subsume      : 9
% 1.89/1.23  #Demod        : 39
% 1.89/1.23  #Tautology    : 54
% 1.89/1.23  #SimpNegUnit  : 4
% 1.89/1.23  #BackRed      : 1
% 1.89/1.23  
% 1.89/1.23  #Partial instantiations: 0
% 1.89/1.23  #Strategies tried      : 1
% 1.89/1.23  
% 1.89/1.23  Timing (in seconds)
% 1.89/1.23  ----------------------
% 1.89/1.23  Preprocessing        : 0.28
% 1.89/1.23  Parsing              : 0.16
% 1.89/1.23  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.19
% 1.89/1.23  Inferencing          : 0.08
% 1.89/1.23  Reduction            : 0.06
% 1.89/1.23  Demodulation         : 0.04
% 1.89/1.23  BG Simplification    : 0.01
% 1.89/1.23  Subsumption          : 0.03
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.50
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
