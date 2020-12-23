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
% DateTime   : Thu Dec  3 10:03:01 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 126 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  109 ( 374 expanded)
%              Number of equality atoms :   56 ( 175 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

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
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

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

tff(c_593,plain,(
    ! [A_67,A_1] :
      ( k1_funct_1('#skF_3'(A_67),'#skF_1'(A_1)) = '#skF_4'
      | A_67 != '#skF_4'
      | A_1 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_299])).

tff(c_420,plain,(
    ! [A_73,A_74] :
      ( k1_funct_1('#skF_3'(A_73),'#skF_1'(A_74)) = k1_xboole_0
      | A_73 != '#skF_4'
      | A_74 != '#skF_4'
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_299])).

tff(c_18,plain,(
    ! [A_14,C_19] :
      ( k1_funct_1('#skF_3'(A_14),C_19) = np__1
      | ~ r2_hidden(C_19,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_423,plain,(
    ! [A_74,A_73] :
      ( np__1 = k1_xboole_0
      | ~ r2_hidden('#skF_1'(A_74),A_73)
      | A_73 != '#skF_4'
      | A_74 != '#skF_4'
      | v1_xboole_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_18])).

tff(c_533,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_553,plain,(
    ! [A_283,C_284] :
      ( k1_funct_1('#skF_3'(A_283),C_284) = k1_xboole_0
      | ~ r2_hidden(C_284,A_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_18])).

tff(c_596,plain,(
    ! [A_1,A_67] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r2_hidden('#skF_1'(A_1),A_67)
      | A_67 != '#skF_4'
      | A_1 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_553])).

tff(c_623,plain,(
    ! [A_292,A_293] :
      ( ~ r2_hidden('#skF_1'(A_292),A_293)
      | A_293 != '#skF_4'
      | A_292 != '#skF_4'
      | v1_xboole_0(A_292) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_596])).

tff(c_631,plain,(
    ! [A_301] :
      ( A_301 != '#skF_4'
      | v1_xboole_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_4,c_623])).

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

tff(c_639,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_631,c_71])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_26])).

tff(c_663,plain,(
    ! [A_320,A_321] :
      ( ~ r2_hidden('#skF_1'(A_320),A_321)
      | A_321 != '#skF_4'
      | A_320 != '#skF_4'
      | v1_xboole_0(A_320) ) ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_671,plain,(
    ! [A_329] :
      ( A_329 != '#skF_4'
      | v1_xboole_0(A_329) ) ),
    inference(resolution,[status(thm)],[c_4,c_663])).

tff(c_684,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_671,c_71])).

tff(c_691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.28  % Computer   : n015.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % DateTime   : Tue Dec  1 11:22:53 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.36  
% 2.26/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.36  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.26/1.36  
% 2.26/1.36  %Foreground sorts:
% 2.26/1.36  
% 2.26/1.36  
% 2.26/1.36  %Background operators:
% 2.26/1.36  
% 2.26/1.36  
% 2.26/1.36  %Foreground operators:
% 2.26/1.36  tff(np__1, type, np__1: $i).
% 2.26/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.36  
% 2.56/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.56/1.37  tff(f_83, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 2.56/1.37  tff(f_52, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.56/1.37  tff(f_64, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.56/1.37  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.56/1.37  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.56/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.37  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.37  tff(c_14, plain, (![A_7, B_8]: (v1_funct_1('#skF_2'(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.37  tff(c_12, plain, (![A_7, B_8]: (k1_relat_1('#skF_2'(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.37  tff(c_16, plain, (![A_7, B_8]: (v1_relat_1('#skF_2'(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.37  tff(c_22, plain, (![A_14]: (v1_funct_1('#skF_3'(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.37  tff(c_20, plain, (![A_14]: (k1_relat_1('#skF_3'(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.37  tff(c_24, plain, (![A_14]: (v1_relat_1('#skF_3'(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.37  tff(c_52, plain, (![C_37, B_38]: (C_37=B_38 | k1_relat_1(C_37)!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.37  tff(c_56, plain, (![B_38, A_14]: (B_38='#skF_3'(A_14) | k1_relat_1('#skF_3'(A_14))!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1('#skF_3'(A_14)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_24, c_52])).
% 2.56/1.37  tff(c_97, plain, (![B_48, A_49]: (B_48='#skF_3'(A_49) | A_49!='#skF_4' | k1_relat_1(B_48)!='#skF_4' | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_56])).
% 2.56/1.37  tff(c_99, plain, (![A_49, A_7, B_8]: ('#skF_3'(A_49)='#skF_2'(A_7, B_8) | A_49!='#skF_4' | k1_relat_1('#skF_2'(A_7, B_8))!='#skF_4' | ~v1_funct_1('#skF_2'(A_7, B_8)))), inference(resolution, [status(thm)], [c_16, c_97])).
% 2.56/1.37  tff(c_178, plain, (![A_57, A_58, B_59]: ('#skF_3'(A_57)='#skF_2'(A_58, B_59) | A_57!='#skF_4' | A_58!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_99])).
% 2.56/1.37  tff(c_10, plain, (![A_7, B_8, D_13]: (k1_funct_1('#skF_2'(A_7, B_8), D_13)=B_8 | ~r2_hidden(D_13, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.37  tff(c_299, plain, (![A_67, D_68, B_69, A_70]: (k1_funct_1('#skF_3'(A_67), D_68)=B_69 | ~r2_hidden(D_68, A_70) | A_67!='#skF_4' | A_70!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_178, c_10])).
% 2.56/1.37  tff(c_593, plain, (![A_67, A_1]: (k1_funct_1('#skF_3'(A_67), '#skF_1'(A_1))='#skF_4' | A_67!='#skF_4' | A_1!='#skF_4' | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_299])).
% 2.56/1.37  tff(c_420, plain, (![A_73, A_74]: (k1_funct_1('#skF_3'(A_73), '#skF_1'(A_74))=k1_xboole_0 | A_73!='#skF_4' | A_74!='#skF_4' | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_4, c_299])).
% 2.56/1.37  tff(c_18, plain, (![A_14, C_19]: (k1_funct_1('#skF_3'(A_14), C_19)=np__1 | ~r2_hidden(C_19, A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.56/1.37  tff(c_423, plain, (![A_74, A_73]: (np__1=k1_xboole_0 | ~r2_hidden('#skF_1'(A_74), A_73) | A_73!='#skF_4' | A_74!='#skF_4' | v1_xboole_0(A_74))), inference(superposition, [status(thm), theory('equality')], [c_420, c_18])).
% 2.56/1.37  tff(c_533, plain, (np__1=k1_xboole_0), inference(splitLeft, [status(thm)], [c_423])).
% 2.56/1.37  tff(c_553, plain, (![A_283, C_284]: (k1_funct_1('#skF_3'(A_283), C_284)=k1_xboole_0 | ~r2_hidden(C_284, A_283))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_18])).
% 2.56/1.37  tff(c_596, plain, (![A_1, A_67]: (k1_xboole_0='#skF_4' | ~r2_hidden('#skF_1'(A_1), A_67) | A_67!='#skF_4' | A_1!='#skF_4' | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_593, c_553])).
% 2.56/1.37  tff(c_623, plain, (![A_292, A_293]: (~r2_hidden('#skF_1'(A_292), A_293) | A_293!='#skF_4' | A_292!='#skF_4' | v1_xboole_0(A_292))), inference(negUnitSimplification, [status(thm)], [c_26, c_596])).
% 2.56/1.37  tff(c_631, plain, (![A_301]: (A_301!='#skF_4' | v1_xboole_0(A_301))), inference(resolution, [status(thm)], [c_4, c_623])).
% 2.56/1.37  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.56/1.37  tff(c_68, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.56/1.37  tff(c_71, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.56/1.37  tff(c_639, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_631, c_71])).
% 2.56/1.37  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_639, c_26])).
% 2.56/1.37  tff(c_663, plain, (![A_320, A_321]: (~r2_hidden('#skF_1'(A_320), A_321) | A_321!='#skF_4' | A_320!='#skF_4' | v1_xboole_0(A_320))), inference(splitRight, [status(thm)], [c_423])).
% 2.56/1.37  tff(c_671, plain, (![A_329]: (A_329!='#skF_4' | v1_xboole_0(A_329))), inference(resolution, [status(thm)], [c_4, c_663])).
% 2.56/1.37  tff(c_684, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_671, c_71])).
% 2.56/1.37  tff(c_691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_684, c_26])).
% 2.56/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.37  
% 2.56/1.37  Inference rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Ref     : 1
% 2.56/1.37  #Sup     : 160
% 2.56/1.37  #Fact    : 0
% 2.56/1.37  #Define  : 0
% 2.56/1.37  #Split   : 1
% 2.56/1.37  #Chain   : 0
% 2.56/1.37  #Close   : 0
% 2.56/1.37  
% 2.56/1.37  Ordering : KBO
% 2.56/1.37  
% 2.56/1.37  Simplification rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Subsume      : 60
% 2.56/1.37  #Demod        : 44
% 2.56/1.37  #Tautology    : 36
% 2.56/1.37  #SimpNegUnit  : 1
% 2.56/1.37  #BackRed      : 11
% 2.56/1.37  
% 2.56/1.37  #Partial instantiations: 248
% 2.56/1.37  #Strategies tried      : 1
% 2.56/1.37  
% 2.56/1.37  Timing (in seconds)
% 2.56/1.37  ----------------------
% 2.56/1.38  Preprocessing        : 0.27
% 2.56/1.38  Parsing              : 0.14
% 2.56/1.38  CNF conversion       : 0.02
% 2.56/1.38  Main loop            : 0.32
% 2.56/1.38  Inferencing          : 0.13
% 2.56/1.38  Reduction            : 0.09
% 2.56/1.38  Demodulation         : 0.06
% 2.56/1.38  BG Simplification    : 0.02
% 2.56/1.38  Subsumption          : 0.07
% 2.56/1.38  Abstraction          : 0.02
% 2.56/1.38  MUC search           : 0.00
% 2.56/1.38  Cooper               : 0.00
% 2.56/1.38  Total                : 0.61
% 2.56/1.38  Index Insertion      : 0.00
% 2.56/1.38  Index Deletion       : 0.00
% 2.56/1.38  Index Matching       : 0.00
% 2.56/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
