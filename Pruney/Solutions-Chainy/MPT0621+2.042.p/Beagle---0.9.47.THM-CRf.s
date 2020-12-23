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
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 155 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 530 expanded)
%              Number of equality atoms :   61 ( 334 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_73,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(c_10,plain,(
    ! [A_3] : v1_funct_1('#skF_1'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3] : k1_relat_1('#skF_1'(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_3] : v1_relat_1('#skF_1'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_9,B_13] :
      ( k1_relat_1('#skF_2'(A_9,B_13)) = A_9
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_9,B_13] :
      ( v1_funct_1('#skF_2'(A_9,B_13))
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_9,B_13] :
      ( v1_relat_1('#skF_2'(A_9,B_13))
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    ! [C_32,B_33] :
      ( C_32 = B_33
      | k1_relat_1(C_32) != '#skF_3'
      | k1_relat_1(B_33) != '#skF_3'
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_161,plain,(
    ! [B_44,A_45,B_46] :
      ( B_44 = '#skF_2'(A_45,B_46)
      | k1_relat_1('#skF_2'(A_45,B_46)) != '#skF_3'
      | k1_relat_1(B_44) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_45,B_46))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | k1_xboole_0 = A_45 ) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_167,plain,(
    ! [B_50,A_51,B_52] :
      ( B_50 = '#skF_2'(A_51,B_52)
      | k1_relat_1('#skF_2'(A_51,B_52)) != '#skF_3'
      | k1_relat_1(B_50) != '#skF_3'
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | k1_xboole_0 = A_51 ) ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_171,plain,(
    ! [B_53,A_54,B_55] :
      ( B_53 = '#skF_2'(A_54,B_55)
      | A_54 != '#skF_3'
      | k1_relat_1(B_53) != '#skF_3'
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | k1_xboole_0 = A_54
      | k1_xboole_0 = A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_175,plain,(
    ! [A_54,B_55,A_3] :
      ( '#skF_2'(A_54,B_55) = '#skF_1'(A_3)
      | A_54 != '#skF_3'
      | k1_relat_1('#skF_1'(A_3)) != '#skF_3'
      | ~ v1_funct_1('#skF_1'(A_3))
      | k1_xboole_0 = A_54 ) ),
    inference(resolution,[status(thm)],[c_12,c_171])).

tff(c_182,plain,(
    ! [A_56,B_57,A_58] :
      ( '#skF_2'(A_56,B_57) = '#skF_1'(A_58)
      | A_56 != '#skF_3'
      | A_58 != '#skF_3'
      | k1_xboole_0 = A_56 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_175])).

tff(c_14,plain,(
    ! [A_9,B_13] :
      ( k2_relat_1('#skF_2'(A_9,B_13)) = k1_tarski(B_13)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_199,plain,(
    ! [A_58,B_57,A_56] :
      ( k2_relat_1('#skF_1'(A_58)) = k1_tarski(B_57)
      | k1_xboole_0 = A_56
      | A_56 != '#skF_3'
      | A_58 != '#skF_3'
      | k1_xboole_0 = A_56 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_14])).

tff(c_274,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_22])).

tff(c_290,plain,(
    ! [A_67,B_68] :
      ( k2_relat_1('#skF_1'(A_67)) = k1_tarski(B_68)
      | A_67 != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_4,plain,(
    ! [A_2] : k1_setfam_1(k1_tarski(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_346,plain,(
    ! [A_69] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_69))) = '#skF_3'
      | A_69 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_4])).

tff(c_298,plain,(
    ! [A_67,B_68] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_67))) = B_68
      | A_67 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_4])).

tff(c_349,plain,(
    ! [B_68,A_69] :
      ( B_68 = '#skF_3'
      | A_69 != '#skF_3'
      | A_69 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_298])).

tff(c_523,plain,(
    ! [A_69] :
      ( A_69 != '#skF_3'
      | A_69 != '#skF_3' ) ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_529,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_523])).

tff(c_531,plain,(
    ! [B_373] : B_373 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_596,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:42:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.34  
% 2.81/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.34  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.81/1.34  
% 2.81/1.34  %Foreground sorts:
% 2.81/1.34  
% 2.81/1.34  
% 2.81/1.34  %Background operators:
% 2.81/1.34  
% 2.81/1.34  
% 2.81/1.34  %Foreground operators:
% 2.81/1.34  tff(np__1, type, np__1: $i).
% 2.81/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.81/1.34  
% 2.81/1.35  tff(f_41, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.81/1.35  tff(f_54, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.81/1.35  tff(f_73, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.81/1.35  tff(f_29, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.81/1.35  tff(c_10, plain, (![A_3]: (v1_funct_1('#skF_1'(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.35  tff(c_8, plain, (![A_3]: (k1_relat_1('#skF_1'(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.36  tff(c_12, plain, (![A_3]: (v1_relat_1('#skF_1'(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.36  tff(c_16, plain, (![A_9, B_13]: (k1_relat_1('#skF_2'(A_9, B_13))=A_9 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.36  tff(c_18, plain, (![A_9, B_13]: (v1_funct_1('#skF_2'(A_9, B_13)) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.36  tff(c_20, plain, (![A_9, B_13]: (v1_relat_1('#skF_2'(A_9, B_13)) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.36  tff(c_66, plain, (![C_32, B_33]: (C_32=B_33 | k1_relat_1(C_32)!='#skF_3' | k1_relat_1(B_33)!='#skF_3' | ~v1_funct_1(C_32) | ~v1_relat_1(C_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.36  tff(c_161, plain, (![B_44, A_45, B_46]: (B_44='#skF_2'(A_45, B_46) | k1_relat_1('#skF_2'(A_45, B_46))!='#skF_3' | k1_relat_1(B_44)!='#skF_3' | ~v1_funct_1('#skF_2'(A_45, B_46)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44) | k1_xboole_0=A_45)), inference(resolution, [status(thm)], [c_20, c_66])).
% 2.81/1.36  tff(c_167, plain, (![B_50, A_51, B_52]: (B_50='#skF_2'(A_51, B_52) | k1_relat_1('#skF_2'(A_51, B_52))!='#skF_3' | k1_relat_1(B_50)!='#skF_3' | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | k1_xboole_0=A_51)), inference(resolution, [status(thm)], [c_18, c_161])).
% 2.81/1.36  tff(c_171, plain, (![B_53, A_54, B_55]: (B_53='#skF_2'(A_54, B_55) | A_54!='#skF_3' | k1_relat_1(B_53)!='#skF_3' | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | k1_xboole_0=A_54 | k1_xboole_0=A_54)), inference(superposition, [status(thm), theory('equality')], [c_16, c_167])).
% 2.81/1.36  tff(c_175, plain, (![A_54, B_55, A_3]: ('#skF_2'(A_54, B_55)='#skF_1'(A_3) | A_54!='#skF_3' | k1_relat_1('#skF_1'(A_3))!='#skF_3' | ~v1_funct_1('#skF_1'(A_3)) | k1_xboole_0=A_54)), inference(resolution, [status(thm)], [c_12, c_171])).
% 2.81/1.36  tff(c_182, plain, (![A_56, B_57, A_58]: ('#skF_2'(A_56, B_57)='#skF_1'(A_58) | A_56!='#skF_3' | A_58!='#skF_3' | k1_xboole_0=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_175])).
% 2.81/1.36  tff(c_14, plain, (![A_9, B_13]: (k2_relat_1('#skF_2'(A_9, B_13))=k1_tarski(B_13) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.36  tff(c_199, plain, (![A_58, B_57, A_56]: (k2_relat_1('#skF_1'(A_58))=k1_tarski(B_57) | k1_xboole_0=A_56 | A_56!='#skF_3' | A_58!='#skF_3' | k1_xboole_0=A_56)), inference(superposition, [status(thm), theory('equality')], [c_182, c_14])).
% 2.81/1.36  tff(c_274, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_199])).
% 2.81/1.36  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.36  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_22])).
% 2.81/1.36  tff(c_290, plain, (![A_67, B_68]: (k2_relat_1('#skF_1'(A_67))=k1_tarski(B_68) | A_67!='#skF_3')), inference(splitRight, [status(thm)], [c_199])).
% 2.81/1.36  tff(c_4, plain, (![A_2]: (k1_setfam_1(k1_tarski(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.36  tff(c_346, plain, (![A_69]: (k1_setfam_1(k2_relat_1('#skF_1'(A_69)))='#skF_3' | A_69!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_290, c_4])).
% 2.81/1.36  tff(c_298, plain, (![A_67, B_68]: (k1_setfam_1(k2_relat_1('#skF_1'(A_67)))=B_68 | A_67!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_290, c_4])).
% 2.81/1.36  tff(c_349, plain, (![B_68, A_69]: (B_68='#skF_3' | A_69!='#skF_3' | A_69!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_346, c_298])).
% 2.81/1.36  tff(c_523, plain, (![A_69]: (A_69!='#skF_3' | A_69!='#skF_3')), inference(splitLeft, [status(thm)], [c_349])).
% 2.81/1.36  tff(c_529, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_523])).
% 2.81/1.36  tff(c_531, plain, (![B_373]: (B_373='#skF_3')), inference(splitRight, [status(thm)], [c_349])).
% 2.81/1.36  tff(c_596, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_531, c_22])).
% 2.81/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.36  
% 2.81/1.36  Inference rules
% 2.81/1.36  ----------------------
% 2.81/1.36  #Ref     : 3
% 2.81/1.36  #Sup     : 161
% 2.81/1.36  #Fact    : 0
% 2.81/1.36  #Define  : 0
% 2.81/1.36  #Split   : 2
% 2.81/1.36  #Chain   : 0
% 2.81/1.36  #Close   : 0
% 2.81/1.36  
% 2.81/1.36  Ordering : KBO
% 2.81/1.36  
% 2.81/1.36  Simplification rules
% 2.81/1.36  ----------------------
% 2.81/1.36  #Subsume      : 57
% 2.81/1.36  #Demod        : 32
% 2.81/1.36  #Tautology    : 28
% 2.81/1.36  #SimpNegUnit  : 0
% 2.81/1.36  #BackRed      : 7
% 2.81/1.36  
% 2.81/1.36  #Partial instantiations: 286
% 2.81/1.36  #Strategies tried      : 1
% 2.81/1.36  
% 2.81/1.36  Timing (in seconds)
% 2.81/1.36  ----------------------
% 2.93/1.36  Preprocessing        : 0.28
% 2.93/1.36  Parsing              : 0.14
% 2.93/1.36  CNF conversion       : 0.02
% 2.93/1.36  Main loop            : 0.32
% 2.93/1.36  Inferencing          : 0.13
% 2.93/1.36  Reduction            : 0.08
% 2.93/1.36  Demodulation         : 0.06
% 2.93/1.36  BG Simplification    : 0.02
% 2.93/1.36  Subsumption          : 0.07
% 2.93/1.36  Abstraction          : 0.02
% 2.93/1.36  MUC search           : 0.00
% 2.93/1.36  Cooper               : 0.00
% 2.93/1.36  Total                : 0.62
% 2.93/1.36  Index Insertion      : 0.00
% 2.93/1.36  Index Deletion       : 0.00
% 2.93/1.36  Index Matching       : 0.00
% 2.93/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
