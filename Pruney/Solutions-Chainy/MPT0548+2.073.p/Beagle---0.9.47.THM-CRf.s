%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:44 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  83 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_71,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_41,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_41])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_57,plain,(
    ! [A_25] :
      ( k7_relat_1(A_25,k1_relat_1(A_25)) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_57])).

tff(c_70,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_66])).

tff(c_162,plain,(
    ! [B_41,A_42] :
      ( k2_relat_1(k7_relat_1(B_41,A_42)) = k9_relat_1(B_41,A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_171,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_162])).

tff(c_178,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_24,c_171])).

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

tff(c_76,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_87,plain,(
    ! [A_13,C_30] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_76])).

tff(c_92,plain,(
    ! [C_31] : ~ r2_hidden(C_31,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_87])).

tff(c_101,plain,(
    ! [B_2] : r1_xboole_0(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,(
    ! [A_35,B_36] :
      ( ~ r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_76])).

tff(c_124,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_117])).

tff(c_356,plain,(
    ! [B_58,A_59] :
      ( k9_relat_1(B_58,k3_xboole_0(k1_relat_1(B_58),A_59)) = k9_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_373,plain,(
    ! [A_59] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_59)) = k9_relat_1(k1_xboole_0,A_59)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_356])).

tff(c_378,plain,(
    ! [A_59] : k9_relat_1(k1_xboole_0,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_178,c_124,c_373])).

tff(c_32,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:34:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.33  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.25/1.33  
% 2.25/1.33  %Foreground sorts:
% 2.25/1.33  
% 2.25/1.33  
% 2.25/1.33  %Background operators:
% 2.25/1.33  
% 2.25/1.33  
% 2.25/1.33  %Foreground operators:
% 2.25/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.25/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.33  
% 2.25/1.34  tff(f_83, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.25/1.34  tff(f_71, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.25/1.34  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.25/1.34  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.25/1.34  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.25/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.25/1.34  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.25/1.34  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.25/1.34  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.25/1.34  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.25/1.34  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 2.25/1.34  tff(f_90, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.25/1.34  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.25/1.34  tff(c_41, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.25/1.34  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_41])).
% 2.25/1.34  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.34  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.34  tff(c_57, plain, (![A_25]: (k7_relat_1(A_25, k1_relat_1(A_25))=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.25/1.34  tff(c_66, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_57])).
% 2.25/1.34  tff(c_70, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_43, c_66])).
% 2.25/1.34  tff(c_162, plain, (![B_41, A_42]: (k2_relat_1(k7_relat_1(B_41, A_42))=k9_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.25/1.34  tff(c_171, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_162])).
% 2.25/1.34  tff(c_178, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_43, c_24, c_171])).
% 2.25/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.25/1.34  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.34  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_76, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.25/1.34  tff(c_87, plain, (![A_13, C_30]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_76])).
% 2.25/1.34  tff(c_92, plain, (![C_31]: (~r2_hidden(C_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_87])).
% 2.25/1.34  tff(c_101, plain, (![B_2]: (r1_xboole_0(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_92])).
% 2.25/1.34  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.25/1.34  tff(c_117, plain, (![A_35, B_36]: (~r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_76])).
% 2.25/1.34  tff(c_124, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_101, c_117])).
% 2.25/1.34  tff(c_356, plain, (![B_58, A_59]: (k9_relat_1(B_58, k3_xboole_0(k1_relat_1(B_58), A_59))=k9_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.25/1.34  tff(c_373, plain, (![A_59]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_59))=k9_relat_1(k1_xboole_0, A_59) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_356])).
% 2.25/1.34  tff(c_378, plain, (![A_59]: (k9_relat_1(k1_xboole_0, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_43, c_178, c_124, c_373])).
% 2.25/1.34  tff(c_32, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.25/1.34  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_32])).
% 2.25/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.34  
% 2.25/1.34  Inference rules
% 2.25/1.34  ----------------------
% 2.25/1.34  #Ref     : 0
% 2.25/1.34  #Sup     : 83
% 2.25/1.34  #Fact    : 0
% 2.25/1.34  #Define  : 0
% 2.25/1.34  #Split   : 0
% 2.25/1.34  #Chain   : 0
% 2.25/1.34  #Close   : 0
% 2.25/1.34  
% 2.25/1.34  Ordering : KBO
% 2.25/1.34  
% 2.25/1.34  Simplification rules
% 2.25/1.34  ----------------------
% 2.25/1.34  #Subsume      : 9
% 2.25/1.34  #Demod        : 44
% 2.25/1.34  #Tautology    : 61
% 2.25/1.34  #SimpNegUnit  : 4
% 2.25/1.34  #BackRed      : 1
% 2.25/1.34  
% 2.25/1.34  #Partial instantiations: 0
% 2.25/1.34  #Strategies tried      : 1
% 2.25/1.34  
% 2.25/1.34  Timing (in seconds)
% 2.25/1.34  ----------------------
% 2.25/1.34  Preprocessing        : 0.31
% 2.25/1.34  Parsing              : 0.18
% 2.25/1.34  CNF conversion       : 0.02
% 2.25/1.34  Main loop            : 0.20
% 2.25/1.34  Inferencing          : 0.09
% 2.25/1.34  Reduction            : 0.06
% 2.25/1.34  Demodulation         : 0.04
% 2.25/1.34  BG Simplification    : 0.01
% 2.25/1.34  Subsumption          : 0.03
% 2.25/1.34  Abstraction          : 0.01
% 2.25/1.34  MUC search           : 0.00
% 2.25/1.34  Cooper               : 0.00
% 2.25/1.34  Total                : 0.54
% 2.25/1.34  Index Insertion      : 0.00
% 2.25/1.34  Index Deletion       : 0.00
% 2.25/1.34  Index Matching       : 0.00
% 2.25/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
