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
% DateTime   : Thu Dec  3 09:59:34 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 243 expanded)
%              Number of equality atoms :   30 (  94 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ! [D] :
                ( v1_relat_1(D)
               => ( ( r1_tarski(k2_relat_1(B),A)
                    & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                    & k5_relat_1(C,D) = k6_relat_1(A) )
                 => D = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_83,plain,(
    ! [B_34,A_35] :
      ( k5_relat_1(B_34,k6_relat_1(A_35)) = B_34
      | ~ r1_tarski(k2_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_92,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_83])).

tff(c_95,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_92])).

tff(c_20,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    k6_relat_1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_3')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_10])).

tff(c_96,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_36,B_37)),k1_relat_1(A_36))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_96])).

tff(c_119,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_10,c_110])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_166,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1(k5_relat_1(A_39,B_40)) = k1_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(A_39),k1_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_170,plain,(
    ! [A_39] :
      ( k1_relat_1(k5_relat_1(A_39,'#skF_3')) = k1_relat_1(A_39)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(A_39),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_122,c_166])).

tff(c_402,plain,(
    ! [A_54] :
      ( k1_relat_1(k5_relat_1(A_54,'#skF_3')) = k1_relat_1(A_54)
      | ~ v1_relat_1(A_54)
      | ~ r1_tarski(k2_relat_1(A_54),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_170])).

tff(c_411,plain,
    ( k1_relat_1(k5_relat_1('#skF_2','#skF_3')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_402])).

tff(c_416,plain,(
    k1_relat_1('#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_56,c_411])).

tff(c_104,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_96])).

tff(c_117,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_104])).

tff(c_14,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_134,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_14])).

tff(c_139,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_134])).

tff(c_420,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_139])).

tff(c_422,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_420])).

tff(c_8,plain,(
    ! [A_10,B_14,C_16] :
      ( k5_relat_1(k5_relat_1(A_10,B_14),C_16) = k5_relat_1(A_10,k5_relat_1(B_14,C_16))
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_517,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_8])).

tff(c_529,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_95,c_20,c_517])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.37  
% 2.39/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.38  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.39/1.38  
% 2.39/1.38  %Foreground sorts:
% 2.39/1.38  
% 2.39/1.38  
% 2.39/1.38  %Background operators:
% 2.39/1.38  
% 2.39/1.38  
% 2.39/1.38  %Foreground operators:
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.39/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.38  
% 2.39/1.39  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => (((r1_tarski(k2_relat_1(B), A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_relat_1)).
% 2.39/1.39  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.39/1.39  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.39/1.39  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.39/1.39  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.39/1.39  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.39/1.39  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.39/1.39  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 2.39/1.39  tff(c_18, plain, ('#skF_2'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.39  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.39  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.39  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.39  tff(c_24, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.39  tff(c_83, plain, (![B_34, A_35]: (k5_relat_1(B_34, k6_relat_1(A_35))=B_34 | ~r1_tarski(k2_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.39  tff(c_92, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_83])).
% 2.39/1.39  tff(c_95, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_92])).
% 2.39/1.39  tff(c_20, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.39  tff(c_22, plain, (k6_relat_1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.39  tff(c_10, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.39/1.39  tff(c_56, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_10])).
% 2.39/1.39  tff(c_96, plain, (![A_36, B_37]: (r1_tarski(k1_relat_1(k5_relat_1(A_36, B_37)), k1_relat_1(A_36)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.39  tff(c_110, plain, (r1_tarski(k1_relat_1(k6_relat_1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_96])).
% 2.39/1.39  tff(c_119, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_10, c_110])).
% 2.39/1.39  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.39  tff(c_122, plain, (![A_1]: (r1_tarski(A_1, k1_relat_1('#skF_3')) | ~r1_tarski(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_119, c_2])).
% 2.39/1.39  tff(c_166, plain, (![A_39, B_40]: (k1_relat_1(k5_relat_1(A_39, B_40))=k1_relat_1(A_39) | ~r1_tarski(k2_relat_1(A_39), k1_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.39  tff(c_170, plain, (![A_39]: (k1_relat_1(k5_relat_1(A_39, '#skF_3'))=k1_relat_1(A_39) | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_39) | ~r1_tarski(k2_relat_1(A_39), '#skF_1'))), inference(resolution, [status(thm)], [c_122, c_166])).
% 2.39/1.39  tff(c_402, plain, (![A_54]: (k1_relat_1(k5_relat_1(A_54, '#skF_3'))=k1_relat_1(A_54) | ~v1_relat_1(A_54) | ~r1_tarski(k2_relat_1(A_54), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_170])).
% 2.39/1.39  tff(c_411, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_402])).
% 2.39/1.39  tff(c_416, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_56, c_411])).
% 2.39/1.39  tff(c_104, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_96])).
% 2.39/1.39  tff(c_117, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_104])).
% 2.39/1.39  tff(c_14, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.39  tff(c_134, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_117, c_14])).
% 2.39/1.39  tff(c_139, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_134])).
% 2.39/1.39  tff(c_420, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_416, c_139])).
% 2.39/1.39  tff(c_422, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_420])).
% 2.39/1.39  tff(c_8, plain, (![A_10, B_14, C_16]: (k5_relat_1(k5_relat_1(A_10, B_14), C_16)=k5_relat_1(A_10, k5_relat_1(B_14, C_16)) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.39/1.39  tff(c_517, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_422, c_8])).
% 2.39/1.39  tff(c_529, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_95, c_20, c_517])).
% 2.39/1.39  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_529])).
% 2.39/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.39  
% 2.39/1.39  Inference rules
% 2.39/1.39  ----------------------
% 2.39/1.39  #Ref     : 0
% 2.39/1.39  #Sup     : 125
% 2.39/1.39  #Fact    : 0
% 2.39/1.39  #Define  : 0
% 2.39/1.39  #Split   : 6
% 2.39/1.39  #Chain   : 0
% 2.39/1.39  #Close   : 0
% 2.39/1.39  
% 2.39/1.39  Ordering : KBO
% 2.39/1.39  
% 2.39/1.39  Simplification rules
% 2.39/1.39  ----------------------
% 2.39/1.39  #Subsume      : 21
% 2.39/1.39  #Demod        : 64
% 2.39/1.39  #Tautology    : 39
% 2.39/1.39  #SimpNegUnit  : 1
% 2.39/1.39  #BackRed      : 4
% 2.39/1.39  
% 2.39/1.39  #Partial instantiations: 0
% 2.39/1.39  #Strategies tried      : 1
% 2.39/1.39  
% 2.39/1.39  Timing (in seconds)
% 2.39/1.39  ----------------------
% 2.39/1.39  Preprocessing        : 0.30
% 2.39/1.39  Parsing              : 0.17
% 2.39/1.39  CNF conversion       : 0.02
% 2.39/1.39  Main loop            : 0.29
% 2.39/1.39  Inferencing          : 0.10
% 2.39/1.39  Reduction            : 0.09
% 2.39/1.39  Demodulation         : 0.07
% 2.39/1.39  BG Simplification    : 0.02
% 2.39/1.39  Subsumption          : 0.06
% 2.39/1.39  Abstraction          : 0.02
% 2.39/1.39  MUC search           : 0.00
% 2.39/1.39  Cooper               : 0.00
% 2.39/1.39  Total                : 0.62
% 2.39/1.39  Index Insertion      : 0.00
% 2.39/1.39  Index Deletion       : 0.00
% 2.39/1.39  Index Matching       : 0.00
% 2.39/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
