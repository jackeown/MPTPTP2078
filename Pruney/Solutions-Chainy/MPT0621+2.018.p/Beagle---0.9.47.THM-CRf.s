%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:01 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 140 expanded)
%              Number of equality atoms :   44 (  65 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_64,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_7,B_8] : v1_funct_1('#skF_2'(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_7,B_8] : k1_relat_1('#skF_2'(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_7,B_8] : v1_relat_1('#skF_2'(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_14] : v1_funct_1('#skF_3'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_14] : k1_relat_1('#skF_3'(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_14] : v1_relat_1('#skF_3'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [C_37,B_38] :
      ( C_37 = B_38
      | k1_relat_1(C_37) != '#skF_4'
      | k1_relat_1(B_38) != '#skF_4'
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    ! [B_38,A_14] :
      ( B_38 = '#skF_3'(A_14)
      | k1_relat_1('#skF_3'(A_14)) != '#skF_4'
      | k1_relat_1(B_38) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_14))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_97,plain,(
    ! [B_48,A_49] :
      ( B_48 = '#skF_3'(A_49)
      | A_49 != '#skF_4'
      | k1_relat_1(B_48) != '#skF_4'
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_56])).

tff(c_99,plain,(
    ! [A_49,A_7,B_8] :
      ( '#skF_3'(A_49) = '#skF_2'(A_7,B_8)
      | A_49 != '#skF_4'
      | k1_relat_1('#skF_2'(A_7,B_8)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_16,c_97])).

tff(c_178,plain,(
    ! [A_57,A_58,B_59] :
      ( '#skF_3'(A_57) = '#skF_2'(A_58,B_59)
      | A_57 != '#skF_4'
      | A_58 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_99])).

tff(c_10,plain,(
    ! [A_7,B_8,D_13] :
      ( k1_funct_1('#skF_2'(A_7,B_8),D_13) = B_8
      | ~ r2_hidden(D_13,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_299,plain,(
    ! [A_67,D_68,B_69,A_70] :
      ( k1_funct_1('#skF_3'(A_67),D_68) = B_69
      | ~ r2_hidden(D_68,A_70)
      | A_67 != '#skF_4'
      | A_70 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_10])).

tff(c_433,plain,(
    ! [A_73,A_74] :
      ( k1_funct_1('#skF_3'(A_73),'#skF_1'(A_74)) = '#skF_4'
      | A_73 != '#skF_4'
      | A_74 != '#skF_4'
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_299])).

tff(c_18,plain,(
    ! [A_14,C_19] :
      ( k1_funct_1('#skF_3'(A_14),C_19) = k1_xboole_0
      | ~ r2_hidden(C_19,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_436,plain,(
    ! [A_74,A_73] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r2_hidden('#skF_1'(A_74),A_73)
      | A_73 != '#skF_4'
      | A_74 != '#skF_4'
      | v1_xboole_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_18])).

tff(c_518,plain,(
    ! [A_265,A_266] :
      ( ~ r2_hidden('#skF_1'(A_265),A_266)
      | A_266 != '#skF_4'
      | A_265 != '#skF_4'
      | v1_xboole_0(A_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_436])).

tff(c_526,plain,(
    ! [A_274] :
      ( A_274 != '#skF_4'
      | v1_xboole_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_4,c_518])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | B_40 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_534,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_526,c_71])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.28  
% 2.29/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.28  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.29/1.28  
% 2.29/1.28  %Foreground sorts:
% 2.29/1.28  
% 2.29/1.28  
% 2.29/1.28  %Background operators:
% 2.29/1.28  
% 2.29/1.28  
% 2.29/1.28  %Foreground operators:
% 2.29/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.29/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.29/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.28  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.29/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.28  
% 2.29/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.29/1.29  tff(f_83, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 2.29/1.29  tff(f_52, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.29/1.29  tff(f_64, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.29/1.29  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.29/1.29  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.29/1.29  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.29  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.29  tff(c_14, plain, (![A_7, B_8]: (v1_funct_1('#skF_2'(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.29  tff(c_12, plain, (![A_7, B_8]: (k1_relat_1('#skF_2'(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.29  tff(c_16, plain, (![A_7, B_8]: (v1_relat_1('#skF_2'(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.29  tff(c_22, plain, (![A_14]: (v1_funct_1('#skF_3'(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.29  tff(c_20, plain, (![A_14]: (k1_relat_1('#skF_3'(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.29  tff(c_24, plain, (![A_14]: (v1_relat_1('#skF_3'(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.29  tff(c_52, plain, (![C_37, B_38]: (C_37=B_38 | k1_relat_1(C_37)!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.29  tff(c_56, plain, (![B_38, A_14]: (B_38='#skF_3'(A_14) | k1_relat_1('#skF_3'(A_14))!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1('#skF_3'(A_14)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_24, c_52])).
% 2.29/1.29  tff(c_97, plain, (![B_48, A_49]: (B_48='#skF_3'(A_49) | A_49!='#skF_4' | k1_relat_1(B_48)!='#skF_4' | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_56])).
% 2.29/1.29  tff(c_99, plain, (![A_49, A_7, B_8]: ('#skF_3'(A_49)='#skF_2'(A_7, B_8) | A_49!='#skF_4' | k1_relat_1('#skF_2'(A_7, B_8))!='#skF_4' | ~v1_funct_1('#skF_2'(A_7, B_8)))), inference(resolution, [status(thm)], [c_16, c_97])).
% 2.29/1.29  tff(c_178, plain, (![A_57, A_58, B_59]: ('#skF_3'(A_57)='#skF_2'(A_58, B_59) | A_57!='#skF_4' | A_58!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_99])).
% 2.29/1.29  tff(c_10, plain, (![A_7, B_8, D_13]: (k1_funct_1('#skF_2'(A_7, B_8), D_13)=B_8 | ~r2_hidden(D_13, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.29  tff(c_299, plain, (![A_67, D_68, B_69, A_70]: (k1_funct_1('#skF_3'(A_67), D_68)=B_69 | ~r2_hidden(D_68, A_70) | A_67!='#skF_4' | A_70!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_178, c_10])).
% 2.29/1.29  tff(c_433, plain, (![A_73, A_74]: (k1_funct_1('#skF_3'(A_73), '#skF_1'(A_74))='#skF_4' | A_73!='#skF_4' | A_74!='#skF_4' | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_4, c_299])).
% 2.29/1.29  tff(c_18, plain, (![A_14, C_19]: (k1_funct_1('#skF_3'(A_14), C_19)=k1_xboole_0 | ~r2_hidden(C_19, A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.29  tff(c_436, plain, (![A_74, A_73]: (k1_xboole_0='#skF_4' | ~r2_hidden('#skF_1'(A_74), A_73) | A_73!='#skF_4' | A_74!='#skF_4' | v1_xboole_0(A_74))), inference(superposition, [status(thm), theory('equality')], [c_433, c_18])).
% 2.29/1.29  tff(c_518, plain, (![A_265, A_266]: (~r2_hidden('#skF_1'(A_265), A_266) | A_266!='#skF_4' | A_265!='#skF_4' | v1_xboole_0(A_265))), inference(negUnitSimplification, [status(thm)], [c_26, c_436])).
% 2.29/1.29  tff(c_526, plain, (![A_274]: (A_274!='#skF_4' | v1_xboole_0(A_274))), inference(resolution, [status(thm)], [c_4, c_518])).
% 2.29/1.29  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.29  tff(c_68, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.29/1.29  tff(c_71, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.29/1.29  tff(c_534, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_526, c_71])).
% 2.29/1.29  tff(c_541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_534, c_26])).
% 2.29/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  Inference rules
% 2.29/1.29  ----------------------
% 2.29/1.29  #Ref     : 1
% 2.29/1.29  #Sup     : 132
% 2.29/1.29  #Fact    : 0
% 2.29/1.29  #Define  : 0
% 2.29/1.29  #Split   : 0
% 2.29/1.29  #Chain   : 0
% 2.29/1.29  #Close   : 0
% 2.29/1.29  
% 2.29/1.29  Ordering : KBO
% 2.29/1.29  
% 2.29/1.29  Simplification rules
% 2.29/1.29  ----------------------
% 2.29/1.29  #Subsume      : 53
% 2.29/1.29  #Demod        : 35
% 2.29/1.29  #Tautology    : 29
% 2.29/1.29  #SimpNegUnit  : 1
% 2.29/1.29  #BackRed      : 4
% 2.29/1.29  
% 2.29/1.29  #Partial instantiations: 175
% 2.29/1.29  #Strategies tried      : 1
% 2.29/1.29  
% 2.29/1.29  Timing (in seconds)
% 2.29/1.29  ----------------------
% 2.29/1.29  Preprocessing        : 0.27
% 2.29/1.29  Parsing              : 0.15
% 2.29/1.29  CNF conversion       : 0.02
% 2.29/1.29  Main loop            : 0.26
% 2.29/1.29  Inferencing          : 0.11
% 2.29/1.29  Reduction            : 0.08
% 2.29/1.29  Demodulation         : 0.05
% 2.29/1.29  BG Simplification    : 0.02
% 2.29/1.29  Subsumption          : 0.05
% 2.29/1.29  Abstraction          : 0.02
% 2.29/1.29  MUC search           : 0.00
% 2.29/1.29  Cooper               : 0.00
% 2.29/1.29  Total                : 0.56
% 2.29/1.29  Index Insertion      : 0.00
% 2.29/1.29  Index Deletion       : 0.00
% 2.29/1.29  Index Matching       : 0.00
% 2.29/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
