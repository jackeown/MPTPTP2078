%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:35 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   53 (  63 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 118 expanded)
%              Number of equality atoms :   41 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_94,plain,(
    ! [B_37,A_38] :
      ( k11_relat_1(B_37,A_38) != k1_xboole_0
      | ~ r2_hidden(A_38,k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_105,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | k1_xboole_0 = A_7
      | k1_tarski(B_8) = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ r2_hidden(B_16,k11_relat_1(C_17,A_15))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    ! [C_50,A_51,B_52] :
      ( k1_funct_1(C_50,A_51) = B_52
      | ~ r2_hidden(k4_tarski(A_51,B_52),C_50)
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [C_56,A_57,B_58] :
      ( k1_funct_1(C_56,A_57) = B_58
      | ~ v1_funct_1(C_56)
      | ~ r2_hidden(B_58,k11_relat_1(C_56,A_57))
      | ~ v1_relat_1(C_56) ) ),
    inference(resolution,[status(thm)],[c_16,c_137])).

tff(c_359,plain,(
    ! [C_88,A_89,B_90] :
      ( '#skF_1'(k11_relat_1(C_88,A_89),B_90) = k1_funct_1(C_88,A_89)
      | ~ v1_funct_1(C_88)
      | ~ v1_relat_1(C_88)
      | k11_relat_1(C_88,A_89) = k1_xboole_0
      | k1_tarski(B_90) = k11_relat_1(C_88,A_89) ) ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( '#skF_1'(A_7,B_8) != B_8
      | k1_xboole_0 = A_7
      | k1_tarski(B_8) = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_367,plain,(
    ! [C_88,A_89,B_90] :
      ( k1_funct_1(C_88,A_89) != B_90
      | k11_relat_1(C_88,A_89) = k1_xboole_0
      | k1_tarski(B_90) = k11_relat_1(C_88,A_89)
      | ~ v1_funct_1(C_88)
      | ~ v1_relat_1(C_88)
      | k11_relat_1(C_88,A_89) = k1_xboole_0
      | k1_tarski(B_90) = k11_relat_1(C_88,A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_8])).

tff(c_731,plain,(
    ! [C_88,A_89] :
      ( k11_relat_1(C_88,A_89) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_88,A_89)) = k11_relat_1(C_88,A_89)
      | ~ v1_funct_1(C_88)
      | ~ v1_relat_1(C_88)
      | k11_relat_1(C_88,A_89) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_88,A_89)) = k11_relat_1(C_88,A_89) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_367])).

tff(c_917,plain,(
    ! [C_129,A_130] :
      ( ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129)
      | k11_relat_1(C_129,A_130) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_129,A_130)) = k11_relat_1(C_129,A_130) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_731])).

tff(c_79,plain,(
    ! [A_33,B_34] :
      ( k9_relat_1(A_33,k1_tarski(B_34)) = k11_relat_1(A_33,B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    ! [B_28,A_29] :
      ( k2_relat_1(k7_relat_1(B_28,A_29)) = k9_relat_1(B_28,A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    k2_relat_1(k7_relat_1('#skF_3',k1_tarski('#skF_2'))) != k1_tarski(k1_funct_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_tarski(k1_funct_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_68,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_tarski(k1_funct_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_62])).

tff(c_85,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k11_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_68])).

tff(c_91,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k11_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_85])).

tff(c_927,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_91])).

tff(c_939,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_927])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.51  
% 3.32/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.51  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.32/1.51  
% 3.32/1.51  %Foreground sorts:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Background operators:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Foreground operators:
% 3.32/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.32/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.32/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.32/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.51  
% 3.47/1.52  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 3.47/1.52  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.47/1.52  tff(f_45, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 3.47/1.52  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.47/1.52  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.47/1.52  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.47/1.52  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.47/1.52  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.52  tff(c_32, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.52  tff(c_94, plain, (![B_37, A_38]: (k11_relat_1(B_37, A_38)!=k1_xboole_0 | ~r2_hidden(A_38, k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.47/1.52  tff(c_101, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_94])).
% 3.47/1.52  tff(c_105, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_101])).
% 3.47/1.52  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.52  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | k1_xboole_0=A_7 | k1_tarski(B_8)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.52  tff(c_16, plain, (![A_15, B_16, C_17]: (r2_hidden(k4_tarski(A_15, B_16), C_17) | ~r2_hidden(B_16, k11_relat_1(C_17, A_15)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.47/1.52  tff(c_137, plain, (![C_50, A_51, B_52]: (k1_funct_1(C_50, A_51)=B_52 | ~r2_hidden(k4_tarski(A_51, B_52), C_50) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.47/1.52  tff(c_156, plain, (![C_56, A_57, B_58]: (k1_funct_1(C_56, A_57)=B_58 | ~v1_funct_1(C_56) | ~r2_hidden(B_58, k11_relat_1(C_56, A_57)) | ~v1_relat_1(C_56))), inference(resolution, [status(thm)], [c_16, c_137])).
% 3.47/1.52  tff(c_359, plain, (![C_88, A_89, B_90]: ('#skF_1'(k11_relat_1(C_88, A_89), B_90)=k1_funct_1(C_88, A_89) | ~v1_funct_1(C_88) | ~v1_relat_1(C_88) | k11_relat_1(C_88, A_89)=k1_xboole_0 | k1_tarski(B_90)=k11_relat_1(C_88, A_89))), inference(resolution, [status(thm)], [c_10, c_156])).
% 3.47/1.52  tff(c_8, plain, (![A_7, B_8]: ('#skF_1'(A_7, B_8)!=B_8 | k1_xboole_0=A_7 | k1_tarski(B_8)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.52  tff(c_367, plain, (![C_88, A_89, B_90]: (k1_funct_1(C_88, A_89)!=B_90 | k11_relat_1(C_88, A_89)=k1_xboole_0 | k1_tarski(B_90)=k11_relat_1(C_88, A_89) | ~v1_funct_1(C_88) | ~v1_relat_1(C_88) | k11_relat_1(C_88, A_89)=k1_xboole_0 | k1_tarski(B_90)=k11_relat_1(C_88, A_89))), inference(superposition, [status(thm), theory('equality')], [c_359, c_8])).
% 3.47/1.52  tff(c_731, plain, (![C_88, A_89]: (k11_relat_1(C_88, A_89)=k1_xboole_0 | k1_tarski(k1_funct_1(C_88, A_89))=k11_relat_1(C_88, A_89) | ~v1_funct_1(C_88) | ~v1_relat_1(C_88) | k11_relat_1(C_88, A_89)=k1_xboole_0 | k1_tarski(k1_funct_1(C_88, A_89))=k11_relat_1(C_88, A_89))), inference(reflexivity, [status(thm), theory('equality')], [c_367])).
% 3.47/1.52  tff(c_917, plain, (![C_129, A_130]: (~v1_funct_1(C_129) | ~v1_relat_1(C_129) | k11_relat_1(C_129, A_130)=k1_xboole_0 | k1_tarski(k1_funct_1(C_129, A_130))=k11_relat_1(C_129, A_130))), inference(factorization, [status(thm), theory('equality')], [c_731])).
% 3.47/1.52  tff(c_79, plain, (![A_33, B_34]: (k9_relat_1(A_33, k1_tarski(B_34))=k11_relat_1(A_33, B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.52  tff(c_56, plain, (![B_28, A_29]: (k2_relat_1(k7_relat_1(B_28, A_29))=k9_relat_1(B_28, A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.47/1.52  tff(c_30, plain, (k2_relat_1(k7_relat_1('#skF_3', k1_tarski('#skF_2')))!=k1_tarski(k1_funct_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.47/1.52  tff(c_62, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_tarski(k1_funct_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_56, c_30])).
% 3.47/1.52  tff(c_68, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_tarski(k1_funct_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_62])).
% 3.47/1.52  tff(c_85, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k11_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_79, c_68])).
% 3.47/1.52  tff(c_91, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k11_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_85])).
% 3.47/1.52  tff(c_927, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_917, c_91])).
% 3.47/1.52  tff(c_939, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_927])).
% 3.47/1.52  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_939])).
% 3.47/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.52  
% 3.47/1.52  Inference rules
% 3.47/1.52  ----------------------
% 3.47/1.52  #Ref     : 1
% 3.47/1.52  #Sup     : 209
% 3.47/1.52  #Fact    : 3
% 3.47/1.52  #Define  : 0
% 3.47/1.52  #Split   : 3
% 3.47/1.52  #Chain   : 0
% 3.47/1.52  #Close   : 0
% 3.47/1.52  
% 3.47/1.52  Ordering : KBO
% 3.47/1.52  
% 3.47/1.52  Simplification rules
% 3.47/1.52  ----------------------
% 3.47/1.52  #Subsume      : 47
% 3.47/1.52  #Demod        : 5
% 3.47/1.52  #Tautology    : 37
% 3.47/1.52  #SimpNegUnit  : 12
% 3.47/1.52  #BackRed      : 0
% 3.47/1.52  
% 3.47/1.52  #Partial instantiations: 0
% 3.47/1.52  #Strategies tried      : 1
% 3.47/1.52  
% 3.47/1.52  Timing (in seconds)
% 3.47/1.52  ----------------------
% 3.47/1.53  Preprocessing        : 0.31
% 3.47/1.53  Parsing              : 0.17
% 3.47/1.53  CNF conversion       : 0.02
% 3.47/1.53  Main loop            : 0.45
% 3.47/1.53  Inferencing          : 0.17
% 3.47/1.53  Reduction            : 0.10
% 3.47/1.53  Demodulation         : 0.06
% 3.47/1.53  BG Simplification    : 0.02
% 3.47/1.53  Subsumption          : 0.13
% 3.47/1.53  Abstraction          : 0.03
% 3.47/1.53  MUC search           : 0.00
% 3.47/1.53  Cooper               : 0.00
% 3.47/1.53  Total                : 0.78
% 3.47/1.53  Index Insertion      : 0.00
% 3.47/1.53  Index Deletion       : 0.00
% 3.47/1.53  Index Matching       : 0.00
% 3.47/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
