%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:01 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 120 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  103 ( 362 expanded)
%              Number of equality atoms :   55 ( 173 expanded)
%              Maximal formula depth    :   10 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_59,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_6,B_7] : v1_funct_1('#skF_2'(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_6,B_7] : k1_relat_1('#skF_2'(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_6,B_7] : v1_relat_1('#skF_2'(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_13] : v1_funct_1('#skF_3'(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_13] : k1_relat_1('#skF_3'(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1('#skF_3'(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ! [C_37,B_38] :
      ( C_37 = B_38
      | k1_relat_1(C_37) != '#skF_4'
      | k1_relat_1(B_38) != '#skF_4'
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [B_38,A_13] :
      ( B_38 = '#skF_3'(A_13)
      | k1_relat_1('#skF_3'(A_13)) != '#skF_4'
      | k1_relat_1(B_38) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_13))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_86,plain,(
    ! [B_45,A_46] :
      ( B_45 = '#skF_3'(A_46)
      | A_46 != '#skF_4'
      | k1_relat_1(B_45) != '#skF_4'
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_55])).

tff(c_88,plain,(
    ! [A_46,A_6,B_7] :
      ( '#skF_3'(A_46) = '#skF_2'(A_6,B_7)
      | A_46 != '#skF_4'
      | k1_relat_1('#skF_2'(A_6,B_7)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_167,plain,(
    ! [A_54,A_55,B_56] :
      ( '#skF_3'(A_54) = '#skF_2'(A_55,B_56)
      | A_54 != '#skF_4'
      | A_55 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_88])).

tff(c_8,plain,(
    ! [A_6,B_7,D_12] :
      ( k1_funct_1('#skF_2'(A_6,B_7),D_12) = B_7
      | ~ r2_hidden(D_12,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_288,plain,(
    ! [A_64,D_65,B_66,A_67] :
      ( k1_funct_1('#skF_3'(A_64),D_65) = B_66
      | ~ r2_hidden(D_65,A_67)
      | A_64 != '#skF_4'
      | A_67 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_557,plain,(
    ! [A_64,A_1] :
      ( k1_funct_1('#skF_3'(A_64),'#skF_1'(A_1)) = '#skF_4'
      | A_64 != '#skF_4'
      | A_1 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_447,plain,(
    ! [A_75,A_76] :
      ( k1_funct_1('#skF_3'(A_75),'#skF_1'(A_76)) = k1_xboole_0
      | A_75 != '#skF_4'
      | A_76 != '#skF_4'
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_16,plain,(
    ! [A_13,C_18] :
      ( k1_funct_1('#skF_3'(A_13),C_18) = np__1
      | ~ r2_hidden(C_18,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_450,plain,(
    ! [A_76,A_75] :
      ( np__1 = k1_xboole_0
      | ~ r2_hidden('#skF_1'(A_76),A_75)
      | A_75 != '#skF_4'
      | A_76 != '#skF_4'
      | v1_xboole_0(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_16])).

tff(c_535,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_542,plain,(
    ! [A_267,C_268] :
      ( k1_funct_1('#skF_3'(A_267),C_268) = k1_xboole_0
      | ~ r2_hidden(C_268,A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_16])).

tff(c_560,plain,(
    ! [A_1,A_64] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r2_hidden('#skF_1'(A_1),A_64)
      | A_64 != '#skF_4'
      | A_1 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_542])).

tff(c_612,plain,(
    ! [A_276,A_277] :
      ( ~ r2_hidden('#skF_1'(A_276),A_277)
      | A_277 != '#skF_4'
      | A_276 != '#skF_4'
      | v1_xboole_0(A_276) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_560])).

tff(c_620,plain,(
    ! [A_285] :
      ( A_285 != '#skF_4'
      | v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_4,c_612])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_625,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_620,c_6])).

tff(c_631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_24])).

tff(c_635,plain,(
    ! [A_293,A_294] :
      ( ~ r2_hidden('#skF_1'(A_293),A_294)
      | A_294 != '#skF_4'
      | A_293 != '#skF_4'
      | v1_xboole_0(A_293) ) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_643,plain,(
    ! [A_302] :
      ( A_302 != '#skF_4'
      | v1_xboole_0(A_302) ) ),
    inference(resolution,[status(thm)],[c_4,c_635])).

tff(c_648,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_643,c_6])).

tff(c_653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff(np__1, type, np__1: $i).
% 2.45/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.45/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.35  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.45/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.35  
% 2.67/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.67/1.37  tff(f_78, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.67/1.37  tff(f_47, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.67/1.37  tff(f_59, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.67/1.37  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.67/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.37  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.37  tff(c_12, plain, (![A_6, B_7]: (v1_funct_1('#skF_2'(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.37  tff(c_10, plain, (![A_6, B_7]: (k1_relat_1('#skF_2'(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.37  tff(c_14, plain, (![A_6, B_7]: (v1_relat_1('#skF_2'(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.37  tff(c_20, plain, (![A_13]: (v1_funct_1('#skF_3'(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.37  tff(c_18, plain, (![A_13]: (k1_relat_1('#skF_3'(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.37  tff(c_22, plain, (![A_13]: (v1_relat_1('#skF_3'(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.37  tff(c_51, plain, (![C_37, B_38]: (C_37=B_38 | k1_relat_1(C_37)!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.37  tff(c_55, plain, (![B_38, A_13]: (B_38='#skF_3'(A_13) | k1_relat_1('#skF_3'(A_13))!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1('#skF_3'(A_13)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.67/1.37  tff(c_86, plain, (![B_45, A_46]: (B_45='#skF_3'(A_46) | A_46!='#skF_4' | k1_relat_1(B_45)!='#skF_4' | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_55])).
% 2.67/1.37  tff(c_88, plain, (![A_46, A_6, B_7]: ('#skF_3'(A_46)='#skF_2'(A_6, B_7) | A_46!='#skF_4' | k1_relat_1('#skF_2'(A_6, B_7))!='#skF_4' | ~v1_funct_1('#skF_2'(A_6, B_7)))), inference(resolution, [status(thm)], [c_14, c_86])).
% 2.67/1.37  tff(c_167, plain, (![A_54, A_55, B_56]: ('#skF_3'(A_54)='#skF_2'(A_55, B_56) | A_54!='#skF_4' | A_55!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_88])).
% 2.67/1.37  tff(c_8, plain, (![A_6, B_7, D_12]: (k1_funct_1('#skF_2'(A_6, B_7), D_12)=B_7 | ~r2_hidden(D_12, A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.37  tff(c_288, plain, (![A_64, D_65, B_66, A_67]: (k1_funct_1('#skF_3'(A_64), D_65)=B_66 | ~r2_hidden(D_65, A_67) | A_64!='#skF_4' | A_67!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_167, c_8])).
% 2.67/1.37  tff(c_557, plain, (![A_64, A_1]: (k1_funct_1('#skF_3'(A_64), '#skF_1'(A_1))='#skF_4' | A_64!='#skF_4' | A_1!='#skF_4' | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_288])).
% 2.67/1.37  tff(c_447, plain, (![A_75, A_76]: (k1_funct_1('#skF_3'(A_75), '#skF_1'(A_76))=k1_xboole_0 | A_75!='#skF_4' | A_76!='#skF_4' | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_288])).
% 2.67/1.37  tff(c_16, plain, (![A_13, C_18]: (k1_funct_1('#skF_3'(A_13), C_18)=np__1 | ~r2_hidden(C_18, A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.37  tff(c_450, plain, (![A_76, A_75]: (np__1=k1_xboole_0 | ~r2_hidden('#skF_1'(A_76), A_75) | A_75!='#skF_4' | A_76!='#skF_4' | v1_xboole_0(A_76))), inference(superposition, [status(thm), theory('equality')], [c_447, c_16])).
% 2.67/1.37  tff(c_535, plain, (np__1=k1_xboole_0), inference(splitLeft, [status(thm)], [c_450])).
% 2.67/1.37  tff(c_542, plain, (![A_267, C_268]: (k1_funct_1('#skF_3'(A_267), C_268)=k1_xboole_0 | ~r2_hidden(C_268, A_267))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_16])).
% 2.67/1.37  tff(c_560, plain, (![A_1, A_64]: (k1_xboole_0='#skF_4' | ~r2_hidden('#skF_1'(A_1), A_64) | A_64!='#skF_4' | A_1!='#skF_4' | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_557, c_542])).
% 2.67/1.37  tff(c_612, plain, (![A_276, A_277]: (~r2_hidden('#skF_1'(A_276), A_277) | A_277!='#skF_4' | A_276!='#skF_4' | v1_xboole_0(A_276))), inference(negUnitSimplification, [status(thm)], [c_24, c_560])).
% 2.67/1.37  tff(c_620, plain, (![A_285]: (A_285!='#skF_4' | v1_xboole_0(A_285))), inference(resolution, [status(thm)], [c_4, c_612])).
% 2.67/1.37  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.37  tff(c_625, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_620, c_6])).
% 2.67/1.37  tff(c_631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_625, c_24])).
% 2.67/1.37  tff(c_635, plain, (![A_293, A_294]: (~r2_hidden('#skF_1'(A_293), A_294) | A_294!='#skF_4' | A_293!='#skF_4' | v1_xboole_0(A_293))), inference(splitRight, [status(thm)], [c_450])).
% 2.67/1.37  tff(c_643, plain, (![A_302]: (A_302!='#skF_4' | v1_xboole_0(A_302))), inference(resolution, [status(thm)], [c_4, c_635])).
% 2.67/1.37  tff(c_648, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_643, c_6])).
% 2.67/1.37  tff(c_653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_648, c_24])).
% 2.67/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  Inference rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Ref     : 1
% 2.67/1.37  #Sup     : 154
% 2.67/1.37  #Fact    : 0
% 2.67/1.37  #Define  : 0
% 2.67/1.37  #Split   : 1
% 2.67/1.37  #Chain   : 0
% 2.67/1.37  #Close   : 0
% 2.67/1.37  
% 2.67/1.37  Ordering : KBO
% 2.67/1.37  
% 2.67/1.37  Simplification rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Subsume      : 61
% 2.67/1.37  #Demod        : 40
% 2.67/1.37  #Tautology    : 33
% 2.67/1.37  #SimpNegUnit  : 1
% 2.67/1.37  #BackRed      : 8
% 2.67/1.37  
% 2.67/1.37  #Partial instantiations: 224
% 2.67/1.37  #Strategies tried      : 1
% 2.67/1.37  
% 2.67/1.37  Timing (in seconds)
% 2.67/1.37  ----------------------
% 2.67/1.37  Preprocessing        : 0.28
% 2.67/1.37  Parsing              : 0.15
% 2.67/1.37  CNF conversion       : 0.02
% 2.67/1.37  Main loop            : 0.32
% 2.67/1.37  Inferencing          : 0.13
% 2.67/1.37  Reduction            : 0.09
% 2.67/1.37  Demodulation         : 0.06
% 2.67/1.37  BG Simplification    : 0.02
% 2.67/1.37  Subsumption          : 0.07
% 2.67/1.37  Abstraction          : 0.02
% 2.67/1.37  MUC search           : 0.00
% 2.67/1.37  Cooper               : 0.00
% 2.67/1.37  Total                : 0.64
% 2.67/1.37  Index Insertion      : 0.00
% 2.67/1.37  Index Deletion       : 0.00
% 2.67/1.37  Index Matching       : 0.00
% 2.67/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
