%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   48 (  69 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 176 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_84,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_65,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_303,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_76)
      | r2_hidden('#skF_2'(A_75,B_76),A_75)
      | B_76 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden(A_52,B_53)
      | ~ r2_hidden(A_52,C_54)
      | r2_hidden(A_52,k5_xboole_0(B_53,C_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_52,A_7] :
      ( r2_hidden(A_52,A_7)
      | ~ r2_hidden(A_52,k1_xboole_0)
      | r2_hidden(A_52,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_365,plain,(
    ! [B_80,A_81] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_80),A_81)
      | r2_hidden('#skF_1'(k1_xboole_0,B_80),B_80)
      | k1_xboole_0 = B_80 ) ),
    inference(resolution,[status(thm)],[c_303,c_122])).

tff(c_16,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),B_5)
      | ~ r2_hidden('#skF_2'(A_4,B_5),B_5)
      | B_5 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_397,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_1'(k1_xboole_0,A_81),A_81)
      | k1_xboole_0 = A_81 ) ),
    inference(resolution,[status(thm)],[c_365,c_16])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_8,B_9] : v1_funct_1('#skF_3'(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_8,B_9] : k1_relat_1('#skF_3'(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_8,B_9] : v1_relat_1('#skF_3'(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_15] : v1_funct_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [A_15] : k1_relat_1('#skF_4'(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [A_15] : v1_relat_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_83,plain,(
    ! [C_39,B_40] :
      ( C_39 = B_40
      | k1_relat_1(C_39) != '#skF_5'
      | k1_relat_1(B_40) != '#skF_5'
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_87,plain,(
    ! [B_40,A_15] :
      ( B_40 = '#skF_4'(A_15)
      | k1_relat_1('#skF_4'(A_15)) != '#skF_5'
      | k1_relat_1(B_40) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_15))
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_38,c_83])).

tff(c_166,plain,(
    ! [B_64,A_65] :
      ( B_64 = '#skF_4'(A_65)
      | A_65 != '#skF_5'
      | k1_relat_1(B_64) != '#skF_5'
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_87])).

tff(c_168,plain,(
    ! [A_65,A_8,B_9] :
      ( '#skF_4'(A_65) = '#skF_3'(A_8,B_9)
      | A_65 != '#skF_5'
      | k1_relat_1('#skF_3'(A_8,B_9)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_235,plain,(
    ! [A_70,A_71,B_72] :
      ( '#skF_4'(A_70) = '#skF_3'(A_71,B_72)
      | A_70 != '#skF_5'
      | A_71 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_168])).

tff(c_24,plain,(
    ! [A_8,B_9,D_14] :
      ( k1_funct_1('#skF_3'(A_8,B_9),D_14) = B_9
      | ~ r2_hidden(D_14,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_513,plain,(
    ! [A_90,D_91,B_92,A_93] :
      ( k1_funct_1('#skF_4'(A_90),D_91) = B_92
      | ~ r2_hidden(D_91,A_93)
      | A_90 != '#skF_5'
      | A_93 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_24])).

tff(c_697,plain,(
    ! [A_102,A_103] :
      ( k1_funct_1('#skF_4'(A_102),'#skF_1'(k1_xboole_0,A_103)) = '#skF_5'
      | A_102 != '#skF_5'
      | A_103 != '#skF_5'
      | k1_xboole_0 = A_103 ) ),
    inference(resolution,[status(thm)],[c_397,c_513])).

tff(c_32,plain,(
    ! [A_15,C_20] :
      ( k1_funct_1('#skF_4'(A_15),C_20) = k1_xboole_0
      | ~ r2_hidden(C_20,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_700,plain,(
    ! [A_103,A_102] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden('#skF_1'(k1_xboole_0,A_103),A_102)
      | A_102 != '#skF_5'
      | A_103 != '#skF_5'
      | k1_xboole_0 = A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_32])).

tff(c_822,plain,(
    ! [A_538,A_539] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,A_538),A_539)
      | A_539 != '#skF_5'
      | A_538 != '#skF_5'
      | k1_xboole_0 = A_538 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_700])).

tff(c_860,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_397,c_822])).

tff(c_871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:03:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.51  
% 2.89/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.52  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 2.89/1.52  
% 2.89/1.52  %Foreground sorts:
% 2.89/1.52  
% 2.89/1.52  
% 2.89/1.52  %Background operators:
% 2.89/1.52  
% 2.89/1.52  
% 2.89/1.52  %Foreground operators:
% 2.89/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.52  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.89/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.89/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.89/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.89/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.52  
% 2.89/1.53  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.89/1.53  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.89/1.53  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.89/1.53  tff(f_84, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.89/1.53  tff(f_53, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.89/1.53  tff(f_65, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.89/1.53  tff(c_303, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), B_76) | r2_hidden('#skF_2'(A_75, B_76), A_75) | B_76=A_75)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.53  tff(c_22, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.53  tff(c_116, plain, (![A_52, B_53, C_54]: (r2_hidden(A_52, B_53) | ~r2_hidden(A_52, C_54) | r2_hidden(A_52, k5_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.89/1.53  tff(c_122, plain, (![A_52, A_7]: (r2_hidden(A_52, A_7) | ~r2_hidden(A_52, k1_xboole_0) | r2_hidden(A_52, A_7))), inference(superposition, [status(thm), theory('equality')], [c_22, c_116])).
% 2.89/1.53  tff(c_365, plain, (![B_80, A_81]: (r2_hidden('#skF_2'(k1_xboole_0, B_80), A_81) | r2_hidden('#skF_1'(k1_xboole_0, B_80), B_80) | k1_xboole_0=B_80)), inference(resolution, [status(thm)], [c_303, c_122])).
% 2.89/1.53  tff(c_16, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), B_5) | ~r2_hidden('#skF_2'(A_4, B_5), B_5) | B_5=A_4)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.53  tff(c_397, plain, (![A_81]: (r2_hidden('#skF_1'(k1_xboole_0, A_81), A_81) | k1_xboole_0=A_81)), inference(resolution, [status(thm)], [c_365, c_16])).
% 2.89/1.53  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.89/1.53  tff(c_28, plain, (![A_8, B_9]: (v1_funct_1('#skF_3'(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.53  tff(c_26, plain, (![A_8, B_9]: (k1_relat_1('#skF_3'(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.53  tff(c_30, plain, (![A_8, B_9]: (v1_relat_1('#skF_3'(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.53  tff(c_36, plain, (![A_15]: (v1_funct_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.53  tff(c_34, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.53  tff(c_38, plain, (![A_15]: (v1_relat_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.53  tff(c_83, plain, (![C_39, B_40]: (C_39=B_40 | k1_relat_1(C_39)!='#skF_5' | k1_relat_1(B_40)!='#skF_5' | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.89/1.53  tff(c_87, plain, (![B_40, A_15]: (B_40='#skF_4'(A_15) | k1_relat_1('#skF_4'(A_15))!='#skF_5' | k1_relat_1(B_40)!='#skF_5' | ~v1_funct_1('#skF_4'(A_15)) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_38, c_83])).
% 2.89/1.53  tff(c_166, plain, (![B_64, A_65]: (B_64='#skF_4'(A_65) | A_65!='#skF_5' | k1_relat_1(B_64)!='#skF_5' | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_87])).
% 2.89/1.53  tff(c_168, plain, (![A_65, A_8, B_9]: ('#skF_4'(A_65)='#skF_3'(A_8, B_9) | A_65!='#skF_5' | k1_relat_1('#skF_3'(A_8, B_9))!='#skF_5' | ~v1_funct_1('#skF_3'(A_8, B_9)))), inference(resolution, [status(thm)], [c_30, c_166])).
% 2.89/1.53  tff(c_235, plain, (![A_70, A_71, B_72]: ('#skF_4'(A_70)='#skF_3'(A_71, B_72) | A_70!='#skF_5' | A_71!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_168])).
% 2.89/1.53  tff(c_24, plain, (![A_8, B_9, D_14]: (k1_funct_1('#skF_3'(A_8, B_9), D_14)=B_9 | ~r2_hidden(D_14, A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.53  tff(c_513, plain, (![A_90, D_91, B_92, A_93]: (k1_funct_1('#skF_4'(A_90), D_91)=B_92 | ~r2_hidden(D_91, A_93) | A_90!='#skF_5' | A_93!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_235, c_24])).
% 2.89/1.53  tff(c_697, plain, (![A_102, A_103]: (k1_funct_1('#skF_4'(A_102), '#skF_1'(k1_xboole_0, A_103))='#skF_5' | A_102!='#skF_5' | A_103!='#skF_5' | k1_xboole_0=A_103)), inference(resolution, [status(thm)], [c_397, c_513])).
% 2.89/1.53  tff(c_32, plain, (![A_15, C_20]: (k1_funct_1('#skF_4'(A_15), C_20)=k1_xboole_0 | ~r2_hidden(C_20, A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.53  tff(c_700, plain, (![A_103, A_102]: (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_1'(k1_xboole_0, A_103), A_102) | A_102!='#skF_5' | A_103!='#skF_5' | k1_xboole_0=A_103)), inference(superposition, [status(thm), theory('equality')], [c_697, c_32])).
% 2.89/1.53  tff(c_822, plain, (![A_538, A_539]: (~r2_hidden('#skF_1'(k1_xboole_0, A_538), A_539) | A_539!='#skF_5' | A_538!='#skF_5' | k1_xboole_0=A_538)), inference(negUnitSimplification, [status(thm)], [c_40, c_700])).
% 2.89/1.53  tff(c_860, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_397, c_822])).
% 2.89/1.53  tff(c_871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_860, c_40])).
% 2.89/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.53  
% 2.89/1.53  Inference rules
% 2.89/1.53  ----------------------
% 2.89/1.53  #Ref     : 1
% 2.89/1.53  #Sup     : 203
% 2.89/1.53  #Fact    : 0
% 2.89/1.53  #Define  : 0
% 2.89/1.53  #Split   : 0
% 2.89/1.53  #Chain   : 0
% 2.89/1.53  #Close   : 0
% 2.89/1.53  
% 2.89/1.53  Ordering : KBO
% 2.89/1.53  
% 2.89/1.53  Simplification rules
% 2.89/1.53  ----------------------
% 2.89/1.53  #Subsume      : 61
% 2.89/1.53  #Demod        : 50
% 2.89/1.53  #Tautology    : 40
% 2.89/1.53  #SimpNegUnit  : 1
% 2.89/1.53  #BackRed      : 7
% 2.89/1.53  
% 2.89/1.53  #Partial instantiations: 324
% 2.89/1.53  #Strategies tried      : 1
% 2.89/1.53  
% 2.89/1.53  Timing (in seconds)
% 2.89/1.53  ----------------------
% 2.89/1.53  Preprocessing        : 0.32
% 2.89/1.53  Parsing              : 0.17
% 2.89/1.53  CNF conversion       : 0.03
% 2.89/1.53  Main loop            : 0.38
% 2.89/1.53  Inferencing          : 0.16
% 2.89/1.53  Reduction            : 0.10
% 2.89/1.53  Demodulation         : 0.07
% 2.89/1.53  BG Simplification    : 0.02
% 2.89/1.53  Subsumption          : 0.08
% 2.89/1.53  Abstraction          : 0.02
% 2.89/1.53  MUC search           : 0.00
% 2.89/1.53  Cooper               : 0.00
% 2.89/1.53  Total                : 0.73
% 2.89/1.53  Index Insertion      : 0.00
% 2.89/1.53  Index Deletion       : 0.00
% 2.89/1.53  Index Matching       : 0.00
% 2.89/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
