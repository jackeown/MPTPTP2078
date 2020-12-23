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
% DateTime   : Thu Dec  3 10:03:03 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 150 expanded)
%              Number of equality atoms :   50 (  78 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_65,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_130,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),B_53)
      | r2_hidden('#skF_2'(A_52,B_53),A_52)
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    ! [A_36,B_37] : ~ r2_hidden(A_36,k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_138,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_53),B_53)
      | k1_xboole_0 = B_53 ) ),
    inference(resolution,[status(thm)],[c_130,c_75])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_8,B_9] : v1_funct_1('#skF_3'(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_8,B_9] : k1_relat_1('#skF_3'(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_8,B_9] : v1_relat_1('#skF_3'(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_15] : v1_funct_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_15] : k1_relat_1('#skF_4'(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [A_15] : v1_relat_1('#skF_4'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_79,plain,(
    ! [C_38,B_39] :
      ( C_38 = B_39
      | k1_relat_1(C_38) != '#skF_5'
      | k1_relat_1(B_39) != '#skF_5'
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_83,plain,(
    ! [B_39,A_15] :
      ( B_39 = '#skF_4'(A_15)
      | k1_relat_1('#skF_4'(A_15)) != '#skF_5'
      | k1_relat_1(B_39) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_15))
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_151,plain,(
    ! [B_55,A_56] :
      ( B_55 = '#skF_4'(A_56)
      | A_56 != '#skF_5'
      | k1_relat_1(B_55) != '#skF_5'
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_83])).

tff(c_153,plain,(
    ! [A_56,A_8,B_9] :
      ( '#skF_4'(A_56) = '#skF_3'(A_8,B_9)
      | A_56 != '#skF_5'
      | k1_relat_1('#skF_3'(A_8,B_9)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_24,c_151])).

tff(c_220,plain,(
    ! [A_61,A_62,B_63] :
      ( '#skF_4'(A_61) = '#skF_3'(A_62,B_63)
      | A_61 != '#skF_5'
      | A_62 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_153])).

tff(c_18,plain,(
    ! [A_8,B_9,D_14] :
      ( k1_funct_1('#skF_3'(A_8,B_9),D_14) = B_9
      | ~ r2_hidden(D_14,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_291,plain,(
    ! [A_68,D_69,B_70,A_71] :
      ( k1_funct_1('#skF_4'(A_68),D_69) = B_70
      | ~ r2_hidden(D_69,A_71)
      | A_68 != '#skF_5'
      | A_71 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_18])).

tff(c_548,plain,(
    ! [A_88,B_89] :
      ( k1_funct_1('#skF_4'(A_88),'#skF_1'(k1_xboole_0,B_89)) = '#skF_5'
      | A_88 != '#skF_5'
      | B_89 != '#skF_5'
      | k1_xboole_0 = B_89 ) ),
    inference(resolution,[status(thm)],[c_138,c_291])).

tff(c_26,plain,(
    ! [A_15,C_20] :
      ( k1_funct_1('#skF_4'(A_15),C_20) = k1_xboole_0
      | ~ r2_hidden(C_20,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_551,plain,(
    ! [B_89,A_88] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden('#skF_1'(k1_xboole_0,B_89),A_88)
      | A_88 != '#skF_5'
      | B_89 != '#skF_5'
      | k1_xboole_0 = B_89 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_26])).

tff(c_659,plain,(
    ! [B_476,A_477] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_476),A_477)
      | A_477 != '#skF_5'
      | B_476 != '#skF_5'
      | k1_xboole_0 = B_476 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_551])).

tff(c_673,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_138,c_659])).

tff(c_684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 2.50/1.35  
% 2.50/1.35  %Foreground sorts:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Background operators:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Foreground operators:
% 2.50/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.35  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.50/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.35  
% 2.50/1.36  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.50/1.36  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.50/1.36  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.50/1.36  tff(f_84, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 2.50/1.36  tff(f_53, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.50/1.36  tff(f_65, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.50/1.36  tff(c_130, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), B_53) | r2_hidden('#skF_2'(A_52, B_53), A_52) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.36  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.36  tff(c_72, plain, (![A_36, B_37]: (~r2_hidden(A_36, k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.36  tff(c_75, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_72])).
% 2.50/1.36  tff(c_138, plain, (![B_53]: (r2_hidden('#skF_1'(k1_xboole_0, B_53), B_53) | k1_xboole_0=B_53)), inference(resolution, [status(thm)], [c_130, c_75])).
% 2.50/1.36  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.50/1.36  tff(c_22, plain, (![A_8, B_9]: (v1_funct_1('#skF_3'(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.36  tff(c_20, plain, (![A_8, B_9]: (k1_relat_1('#skF_3'(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.36  tff(c_24, plain, (![A_8, B_9]: (v1_relat_1('#skF_3'(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.36  tff(c_30, plain, (![A_15]: (v1_funct_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.50/1.36  tff(c_28, plain, (![A_15]: (k1_relat_1('#skF_4'(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.50/1.36  tff(c_32, plain, (![A_15]: (v1_relat_1('#skF_4'(A_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.50/1.36  tff(c_79, plain, (![C_38, B_39]: (C_38=B_39 | k1_relat_1(C_38)!='#skF_5' | k1_relat_1(B_39)!='#skF_5' | ~v1_funct_1(C_38) | ~v1_relat_1(C_38) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.50/1.36  tff(c_83, plain, (![B_39, A_15]: (B_39='#skF_4'(A_15) | k1_relat_1('#skF_4'(A_15))!='#skF_5' | k1_relat_1(B_39)!='#skF_5' | ~v1_funct_1('#skF_4'(A_15)) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_32, c_79])).
% 2.50/1.36  tff(c_151, plain, (![B_55, A_56]: (B_55='#skF_4'(A_56) | A_56!='#skF_5' | k1_relat_1(B_55)!='#skF_5' | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_83])).
% 2.50/1.36  tff(c_153, plain, (![A_56, A_8, B_9]: ('#skF_4'(A_56)='#skF_3'(A_8, B_9) | A_56!='#skF_5' | k1_relat_1('#skF_3'(A_8, B_9))!='#skF_5' | ~v1_funct_1('#skF_3'(A_8, B_9)))), inference(resolution, [status(thm)], [c_24, c_151])).
% 2.50/1.36  tff(c_220, plain, (![A_61, A_62, B_63]: ('#skF_4'(A_61)='#skF_3'(A_62, B_63) | A_61!='#skF_5' | A_62!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_153])).
% 2.50/1.36  tff(c_18, plain, (![A_8, B_9, D_14]: (k1_funct_1('#skF_3'(A_8, B_9), D_14)=B_9 | ~r2_hidden(D_14, A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.36  tff(c_291, plain, (![A_68, D_69, B_70, A_71]: (k1_funct_1('#skF_4'(A_68), D_69)=B_70 | ~r2_hidden(D_69, A_71) | A_68!='#skF_5' | A_71!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_220, c_18])).
% 2.50/1.36  tff(c_548, plain, (![A_88, B_89]: (k1_funct_1('#skF_4'(A_88), '#skF_1'(k1_xboole_0, B_89))='#skF_5' | A_88!='#skF_5' | B_89!='#skF_5' | k1_xboole_0=B_89)), inference(resolution, [status(thm)], [c_138, c_291])).
% 2.50/1.36  tff(c_26, plain, (![A_15, C_20]: (k1_funct_1('#skF_4'(A_15), C_20)=k1_xboole_0 | ~r2_hidden(C_20, A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.50/1.36  tff(c_551, plain, (![B_89, A_88]: (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_1'(k1_xboole_0, B_89), A_88) | A_88!='#skF_5' | B_89!='#skF_5' | k1_xboole_0=B_89)), inference(superposition, [status(thm), theory('equality')], [c_548, c_26])).
% 2.50/1.36  tff(c_659, plain, (![B_476, A_477]: (~r2_hidden('#skF_1'(k1_xboole_0, B_476), A_477) | A_477!='#skF_5' | B_476!='#skF_5' | k1_xboole_0=B_476)), inference(negUnitSimplification, [status(thm)], [c_34, c_551])).
% 2.50/1.36  tff(c_673, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_138, c_659])).
% 2.50/1.36  tff(c_684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_673, c_34])).
% 2.50/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.36  
% 2.50/1.36  Inference rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Ref     : 1
% 2.50/1.36  #Sup     : 162
% 2.50/1.36  #Fact    : 0
% 2.50/1.36  #Define  : 0
% 2.50/1.36  #Split   : 0
% 2.50/1.36  #Chain   : 0
% 2.50/1.36  #Close   : 0
% 2.50/1.36  
% 2.50/1.36  Ordering : KBO
% 2.50/1.36  
% 2.50/1.36  Simplification rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Subsume      : 56
% 2.50/1.36  #Demod        : 46
% 2.50/1.36  #Tautology    : 35
% 2.50/1.36  #SimpNegUnit  : 2
% 2.50/1.36  #BackRed      : 7
% 2.50/1.36  
% 2.50/1.36  #Partial instantiations: 279
% 2.50/1.36  #Strategies tried      : 1
% 2.50/1.36  
% 2.50/1.36  Timing (in seconds)
% 2.50/1.36  ----------------------
% 2.50/1.36  Preprocessing        : 0.28
% 2.50/1.36  Parsing              : 0.15
% 2.50/1.36  CNF conversion       : 0.02
% 2.50/1.36  Main loop            : 0.30
% 2.50/1.36  Inferencing          : 0.12
% 2.50/1.36  Reduction            : 0.09
% 2.50/1.36  Demodulation         : 0.06
% 2.50/1.36  BG Simplification    : 0.02
% 2.50/1.36  Subsumption          : 0.06
% 2.50/1.36  Abstraction          : 0.02
% 2.50/1.36  MUC search           : 0.00
% 2.50/1.36  Cooper               : 0.00
% 2.50/1.36  Total                : 0.61
% 2.50/1.36  Index Insertion      : 0.00
% 2.50/1.36  Index Deletion       : 0.00
% 2.50/1.36  Index Matching       : 0.00
% 2.50/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
