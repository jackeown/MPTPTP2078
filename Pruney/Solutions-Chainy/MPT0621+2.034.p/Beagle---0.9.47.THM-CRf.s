%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:03 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 246 expanded)
%              Number of equality atoms :   54 ( 106 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_80,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_356,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r2_hidden('#skF_1'(A_78,B_79,C_80),B_79)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k4_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_363,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_356])).

tff(c_365,plain,(
    ! [A_81,C_82] :
      ( r2_hidden('#skF_2'(A_81,A_81,C_82),C_82)
      | k4_xboole_0(A_81,A_81) = C_82 ) ),
    inference(resolution,[status(thm)],[c_18,c_356])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [D_44,B_45,A_46] :
      ( ~ r2_hidden(D_44,B_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [D_44,A_7] :
      ( ~ r2_hidden(D_44,k1_xboole_0)
      | ~ r2_hidden(D_44,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_96])).

tff(c_383,plain,(
    ! [A_83,A_84] :
      ( ~ r2_hidden('#skF_2'(A_83,A_83,k1_xboole_0),A_84)
      | k4_xboole_0(A_83,A_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_365,c_99])).

tff(c_394,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_363,c_383])).

tff(c_397,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k1_xboole_0 = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_363])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_430,plain,(
    ! [A_88,C_89] :
      ( r2_hidden('#skF_2'(A_88,A_88,C_89),C_89)
      | k1_xboole_0 = C_89 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_363])).

tff(c_34,plain,(
    ! [A_15] : v1_funct_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_15] : k1_relat_1('#skF_4'(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_15] : v1_relat_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_8,B_9] : v1_funct_1('#skF_3'(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_8,B_9] : k1_relat_1('#skF_3'(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_8,B_9] : v1_relat_1('#skF_3'(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_81,plain,(
    ! [C_39,B_40] :
      ( C_39 = B_40
      | k1_relat_1(C_39) != '#skF_5'
      | k1_relat_1(B_40) != '#skF_5'
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_83,plain,(
    ! [B_40,A_8,B_9] :
      ( B_40 = '#skF_3'(A_8,B_9)
      | k1_relat_1('#skF_3'(A_8,B_9)) != '#skF_5'
      | k1_relat_1(B_40) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_8,B_9))
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_218,plain,(
    ! [B_64,A_65,B_66] :
      ( B_64 = '#skF_3'(A_65,B_66)
      | A_65 != '#skF_5'
      | k1_relat_1(B_64) != '#skF_5'
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_83])).

tff(c_222,plain,(
    ! [A_15,A_65,B_66] :
      ( '#skF_4'(A_15) = '#skF_3'(A_65,B_66)
      | A_65 != '#skF_5'
      | k1_relat_1('#skF_4'(A_15)) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_15)) ) ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_230,plain,(
    ! [A_67,A_68,B_69] :
      ( '#skF_4'(A_67) = '#skF_3'(A_68,B_69)
      | A_68 != '#skF_5'
      | A_67 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_222])).

tff(c_22,plain,(
    ! [A_8,B_9,D_14] :
      ( k1_funct_1('#skF_3'(A_8,B_9),D_14) = B_9
      | ~ r2_hidden(D_14,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_245,plain,(
    ! [A_67,D_14,B_69,A_68] :
      ( k1_funct_1('#skF_4'(A_67),D_14) = B_69
      | ~ r2_hidden(D_14,A_68)
      | A_68 != '#skF_5'
      | A_67 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_22])).

tff(c_828,plain,(
    ! [A_114,A_115,C_116] :
      ( k1_funct_1('#skF_4'(A_114),'#skF_2'(A_115,A_115,C_116)) = '#skF_5'
      | C_116 != '#skF_5'
      | A_114 != '#skF_5'
      | k1_xboole_0 = C_116 ) ),
    inference(resolution,[status(thm)],[c_430,c_245])).

tff(c_30,plain,(
    ! [A_15,C_20] :
      ( k1_funct_1('#skF_4'(A_15),C_20) = k1_xboole_0
      | ~ r2_hidden(C_20,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_831,plain,(
    ! [A_115,C_116,A_114] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_115,A_115,C_116),A_114)
      | C_116 != '#skF_5'
      | A_114 != '#skF_5'
      | k1_xboole_0 = C_116 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_30])).

tff(c_923,plain,(
    ! [A_663,C_664,A_665] :
      ( ~ r2_hidden('#skF_2'(A_663,A_663,C_664),A_665)
      | C_664 != '#skF_5'
      | A_665 != '#skF_5'
      | k1_xboole_0 = C_664 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_831])).

tff(c_951,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_397,c_923])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 2.73/1.43  
% 2.73/1.43  %Foreground sorts:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Background operators:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Foreground operators:
% 2.73/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.73/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.43  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.73/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.44  
% 2.73/1.45  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.73/1.45  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.73/1.45  tff(f_80, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.73/1.45  tff(f_61, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.73/1.45  tff(f_49, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.73/1.45  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.45  tff(c_356, plain, (![A_78, B_79, C_80]: (~r2_hidden('#skF_1'(A_78, B_79, C_80), B_79) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k4_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.45  tff(c_363, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_356])).
% 2.73/1.45  tff(c_365, plain, (![A_81, C_82]: (r2_hidden('#skF_2'(A_81, A_81, C_82), C_82) | k4_xboole_0(A_81, A_81)=C_82)), inference(resolution, [status(thm)], [c_18, c_356])).
% 2.73/1.45  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.45  tff(c_96, plain, (![D_44, B_45, A_46]: (~r2_hidden(D_44, B_45) | ~r2_hidden(D_44, k4_xboole_0(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.45  tff(c_99, plain, (![D_44, A_7]: (~r2_hidden(D_44, k1_xboole_0) | ~r2_hidden(D_44, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_96])).
% 2.73/1.45  tff(c_383, plain, (![A_83, A_84]: (~r2_hidden('#skF_2'(A_83, A_83, k1_xboole_0), A_84) | k4_xboole_0(A_83, A_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_365, c_99])).
% 2.73/1.45  tff(c_394, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_363, c_383])).
% 2.73/1.45  tff(c_397, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k1_xboole_0=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_363])).
% 2.73/1.45  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.45  tff(c_430, plain, (![A_88, C_89]: (r2_hidden('#skF_2'(A_88, A_88, C_89), C_89) | k1_xboole_0=C_89)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_363])).
% 2.73/1.45  tff(c_34, plain, (![A_15]: (v1_funct_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.45  tff(c_32, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.45  tff(c_36, plain, (![A_15]: (v1_relat_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.45  tff(c_26, plain, (![A_8, B_9]: (v1_funct_1('#skF_3'(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.45  tff(c_24, plain, (![A_8, B_9]: (k1_relat_1('#skF_3'(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.45  tff(c_28, plain, (![A_8, B_9]: (v1_relat_1('#skF_3'(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.45  tff(c_81, plain, (![C_39, B_40]: (C_39=B_40 | k1_relat_1(C_39)!='#skF_5' | k1_relat_1(B_40)!='#skF_5' | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.45  tff(c_83, plain, (![B_40, A_8, B_9]: (B_40='#skF_3'(A_8, B_9) | k1_relat_1('#skF_3'(A_8, B_9))!='#skF_5' | k1_relat_1(B_40)!='#skF_5' | ~v1_funct_1('#skF_3'(A_8, B_9)) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.73/1.45  tff(c_218, plain, (![B_64, A_65, B_66]: (B_64='#skF_3'(A_65, B_66) | A_65!='#skF_5' | k1_relat_1(B_64)!='#skF_5' | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_83])).
% 2.73/1.45  tff(c_222, plain, (![A_15, A_65, B_66]: ('#skF_4'(A_15)='#skF_3'(A_65, B_66) | A_65!='#skF_5' | k1_relat_1('#skF_4'(A_15))!='#skF_5' | ~v1_funct_1('#skF_4'(A_15)))), inference(resolution, [status(thm)], [c_36, c_218])).
% 2.73/1.45  tff(c_230, plain, (![A_67, A_68, B_69]: ('#skF_4'(A_67)='#skF_3'(A_68, B_69) | A_68!='#skF_5' | A_67!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_222])).
% 2.73/1.45  tff(c_22, plain, (![A_8, B_9, D_14]: (k1_funct_1('#skF_3'(A_8, B_9), D_14)=B_9 | ~r2_hidden(D_14, A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.45  tff(c_245, plain, (![A_67, D_14, B_69, A_68]: (k1_funct_1('#skF_4'(A_67), D_14)=B_69 | ~r2_hidden(D_14, A_68) | A_68!='#skF_5' | A_67!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_230, c_22])).
% 2.73/1.45  tff(c_828, plain, (![A_114, A_115, C_116]: (k1_funct_1('#skF_4'(A_114), '#skF_2'(A_115, A_115, C_116))='#skF_5' | C_116!='#skF_5' | A_114!='#skF_5' | k1_xboole_0=C_116)), inference(resolution, [status(thm)], [c_430, c_245])).
% 2.73/1.45  tff(c_30, plain, (![A_15, C_20]: (k1_funct_1('#skF_4'(A_15), C_20)=k1_xboole_0 | ~r2_hidden(C_20, A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.45  tff(c_831, plain, (![A_115, C_116, A_114]: (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_2'(A_115, A_115, C_116), A_114) | C_116!='#skF_5' | A_114!='#skF_5' | k1_xboole_0=C_116)), inference(superposition, [status(thm), theory('equality')], [c_828, c_30])).
% 2.73/1.45  tff(c_923, plain, (![A_663, C_664, A_665]: (~r2_hidden('#skF_2'(A_663, A_663, C_664), A_665) | C_664!='#skF_5' | A_665!='#skF_5' | k1_xboole_0=C_664)), inference(negUnitSimplification, [status(thm)], [c_38, c_831])).
% 2.73/1.45  tff(c_951, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_397, c_923])).
% 2.73/1.45  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_951, c_38])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 1
% 2.73/1.45  #Sup     : 224
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 0
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 65
% 2.73/1.45  #Demod        : 68
% 2.73/1.45  #Tautology    : 57
% 2.73/1.45  #SimpNegUnit  : 1
% 2.73/1.45  #BackRed      : 12
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 342
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.73/1.45  Preprocessing        : 0.30
% 2.73/1.45  Parsing              : 0.16
% 2.73/1.45  CNF conversion       : 0.02
% 2.73/1.45  Main loop            : 0.38
% 2.73/1.45  Inferencing          : 0.15
% 2.73/1.45  Reduction            : 0.10
% 2.73/1.45  Demodulation         : 0.07
% 2.73/1.45  BG Simplification    : 0.02
% 2.73/1.45  Subsumption          : 0.08
% 2.73/1.45  Abstraction          : 0.02
% 2.73/1.45  MUC search           : 0.00
% 2.73/1.45  Cooper               : 0.00
% 2.73/1.45  Total                : 0.71
% 2.73/1.45  Index Insertion      : 0.00
% 2.73/1.45  Index Deletion       : 0.00
% 2.73/1.45  Index Matching       : 0.00
% 2.73/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
