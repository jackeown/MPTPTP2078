%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:03 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 160 expanded)
%              Number of equality atoms :   53 (  84 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_89,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_70,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_291,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_1'(A_73,B_74,C_75),A_73)
      | r2_hidden('#skF_2'(A_73,B_74,C_75),C_75)
      | k4_xboole_0(A_73,B_74) = C_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,(
    ! [A_43,B_44] : ~ r2_hidden(A_43,k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_303,plain,(
    ! [B_74,C_75] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_74,C_75),C_75)
      | k4_xboole_0(k1_xboole_0,B_74) = C_75 ) ),
    inference(resolution,[status(thm)],[c_291,c_105])).

tff(c_317,plain,(
    ! [B_74,C_75] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_74,C_75),C_75)
      | k1_xboole_0 = C_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_303])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_12,B_13] : v1_funct_1('#skF_3'(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_12,B_13] : k1_relat_1('#skF_3'(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_12,B_13] : v1_relat_1('#skF_3'(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_19] : v1_funct_1('#skF_4'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [A_19] : k1_relat_1('#skF_4'(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    ! [A_19] : v1_relat_1('#skF_4'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,(
    ! [C_41,B_42] :
      ( C_41 = B_42
      | k1_relat_1(C_41) != '#skF_5'
      | k1_relat_1(B_42) != '#skF_5'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_95,plain,(
    ! [B_42,A_19] :
      ( B_42 = '#skF_4'(A_19)
      | k1_relat_1('#skF_4'(A_19)) != '#skF_5'
      | k1_relat_1(B_42) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_19))
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_44,c_91])).

tff(c_158,plain,(
    ! [B_61,A_62] :
      ( B_61 = '#skF_4'(A_62)
      | A_62 != '#skF_5'
      | k1_relat_1(B_61) != '#skF_5'
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_95])).

tff(c_160,plain,(
    ! [A_62,A_12,B_13] :
      ( '#skF_4'(A_62) = '#skF_3'(A_12,B_13)
      | A_62 != '#skF_5'
      | k1_relat_1('#skF_3'(A_12,B_13)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_36,c_158])).

tff(c_227,plain,(
    ! [A_67,A_68,B_69] :
      ( '#skF_4'(A_67) = '#skF_3'(A_68,B_69)
      | A_67 != '#skF_5'
      | A_68 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_160])).

tff(c_30,plain,(
    ! [A_12,B_13,D_18] :
      ( k1_funct_1('#skF_3'(A_12,B_13),D_18) = B_13
      | ~ r2_hidden(D_18,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_338,plain,(
    ! [A_78,D_79,B_80,A_81] :
      ( k1_funct_1('#skF_4'(A_78),D_79) = B_80
      | ~ r2_hidden(D_79,A_81)
      | A_78 != '#skF_5'
      | A_81 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_30])).

tff(c_731,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_funct_1('#skF_4'(A_110),'#skF_2'(k1_xboole_0,B_111,C_112)) = '#skF_5'
      | A_110 != '#skF_5'
      | C_112 != '#skF_5'
      | k1_xboole_0 = C_112 ) ),
    inference(resolution,[status(thm)],[c_317,c_338])).

tff(c_38,plain,(
    ! [A_19,C_24] :
      ( k1_funct_1('#skF_4'(A_19),C_24) = k1_xboole_0
      | ~ r2_hidden(C_24,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_734,plain,(
    ! [B_111,C_112,A_110] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden('#skF_2'(k1_xboole_0,B_111,C_112),A_110)
      | A_110 != '#skF_5'
      | C_112 != '#skF_5'
      | k1_xboole_0 = C_112 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_38])).

tff(c_856,plain,(
    ! [B_719,C_720,A_721] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_719,C_720),A_721)
      | A_721 != '#skF_5'
      | C_720 != '#skF_5'
      | k1_xboole_0 = C_720 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_734])).

tff(c_885,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_317,c_856])).

tff(c_900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.48  
% 2.93/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.48  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 2.93/1.48  
% 2.93/1.48  %Foreground sorts:
% 2.93/1.48  
% 2.93/1.48  
% 2.93/1.48  %Background operators:
% 2.93/1.48  
% 2.93/1.48  
% 2.93/1.48  %Foreground operators:
% 2.93/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.93/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.93/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.93/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.93/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.93/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.93/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.93/1.48  
% 2.93/1.50  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.93/1.50  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.93/1.50  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.93/1.50  tff(f_46, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.93/1.50  tff(f_89, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.93/1.50  tff(f_58, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.93/1.50  tff(f_70, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.93/1.50  tff(c_20, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.50  tff(c_291, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_1'(A_73, B_74, C_75), A_73) | r2_hidden('#skF_2'(A_73, B_74, C_75), C_75) | k4_xboole_0(A_73, B_74)=C_75)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.50  tff(c_24, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.50  tff(c_102, plain, (![A_43, B_44]: (~r2_hidden(A_43, k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.93/1.50  tff(c_105, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_102])).
% 2.93/1.50  tff(c_303, plain, (![B_74, C_75]: (r2_hidden('#skF_2'(k1_xboole_0, B_74, C_75), C_75) | k4_xboole_0(k1_xboole_0, B_74)=C_75)), inference(resolution, [status(thm)], [c_291, c_105])).
% 2.93/1.50  tff(c_317, plain, (![B_74, C_75]: (r2_hidden('#skF_2'(k1_xboole_0, B_74, C_75), C_75) | k1_xboole_0=C_75)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_303])).
% 2.93/1.50  tff(c_46, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.50  tff(c_34, plain, (![A_12, B_13]: (v1_funct_1('#skF_3'(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.50  tff(c_32, plain, (![A_12, B_13]: (k1_relat_1('#skF_3'(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.50  tff(c_36, plain, (![A_12, B_13]: (v1_relat_1('#skF_3'(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.50  tff(c_42, plain, (![A_19]: (v1_funct_1('#skF_4'(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.93/1.50  tff(c_40, plain, (![A_19]: (k1_relat_1('#skF_4'(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.93/1.50  tff(c_44, plain, (![A_19]: (v1_relat_1('#skF_4'(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.93/1.50  tff(c_91, plain, (![C_41, B_42]: (C_41=B_42 | k1_relat_1(C_41)!='#skF_5' | k1_relat_1(B_42)!='#skF_5' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.50  tff(c_95, plain, (![B_42, A_19]: (B_42='#skF_4'(A_19) | k1_relat_1('#skF_4'(A_19))!='#skF_5' | k1_relat_1(B_42)!='#skF_5' | ~v1_funct_1('#skF_4'(A_19)) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_44, c_91])).
% 2.93/1.50  tff(c_158, plain, (![B_61, A_62]: (B_61='#skF_4'(A_62) | A_62!='#skF_5' | k1_relat_1(B_61)!='#skF_5' | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_95])).
% 2.93/1.50  tff(c_160, plain, (![A_62, A_12, B_13]: ('#skF_4'(A_62)='#skF_3'(A_12, B_13) | A_62!='#skF_5' | k1_relat_1('#skF_3'(A_12, B_13))!='#skF_5' | ~v1_funct_1('#skF_3'(A_12, B_13)))), inference(resolution, [status(thm)], [c_36, c_158])).
% 2.93/1.50  tff(c_227, plain, (![A_67, A_68, B_69]: ('#skF_4'(A_67)='#skF_3'(A_68, B_69) | A_67!='#skF_5' | A_68!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_160])).
% 2.93/1.50  tff(c_30, plain, (![A_12, B_13, D_18]: (k1_funct_1('#skF_3'(A_12, B_13), D_18)=B_13 | ~r2_hidden(D_18, A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.93/1.50  tff(c_338, plain, (![A_78, D_79, B_80, A_81]: (k1_funct_1('#skF_4'(A_78), D_79)=B_80 | ~r2_hidden(D_79, A_81) | A_78!='#skF_5' | A_81!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_227, c_30])).
% 2.93/1.50  tff(c_731, plain, (![A_110, B_111, C_112]: (k1_funct_1('#skF_4'(A_110), '#skF_2'(k1_xboole_0, B_111, C_112))='#skF_5' | A_110!='#skF_5' | C_112!='#skF_5' | k1_xboole_0=C_112)), inference(resolution, [status(thm)], [c_317, c_338])).
% 2.93/1.50  tff(c_38, plain, (![A_19, C_24]: (k1_funct_1('#skF_4'(A_19), C_24)=k1_xboole_0 | ~r2_hidden(C_24, A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.93/1.50  tff(c_734, plain, (![B_111, C_112, A_110]: (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_2'(k1_xboole_0, B_111, C_112), A_110) | A_110!='#skF_5' | C_112!='#skF_5' | k1_xboole_0=C_112)), inference(superposition, [status(thm), theory('equality')], [c_731, c_38])).
% 2.93/1.50  tff(c_856, plain, (![B_719, C_720, A_721]: (~r2_hidden('#skF_2'(k1_xboole_0, B_719, C_720), A_721) | A_721!='#skF_5' | C_720!='#skF_5' | k1_xboole_0=C_720)), inference(negUnitSimplification, [status(thm)], [c_46, c_734])).
% 2.93/1.50  tff(c_885, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_317, c_856])).
% 2.93/1.50  tff(c_900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_885, c_46])).
% 2.93/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.50  
% 2.93/1.50  Inference rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Ref     : 1
% 2.93/1.50  #Sup     : 212
% 2.93/1.50  #Fact    : 0
% 2.93/1.50  #Define  : 0
% 2.93/1.50  #Split   : 0
% 2.93/1.50  #Chain   : 0
% 2.93/1.50  #Close   : 0
% 2.93/1.50  
% 2.93/1.50  Ordering : KBO
% 2.93/1.50  
% 2.93/1.50  Simplification rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Subsume      : 63
% 2.93/1.50  #Demod        : 62
% 2.93/1.50  #Tautology    : 48
% 2.93/1.50  #SimpNegUnit  : 6
% 2.93/1.50  #BackRed      : 11
% 2.93/1.50  
% 2.93/1.50  #Partial instantiations: 370
% 2.93/1.50  #Strategies tried      : 1
% 2.93/1.50  
% 2.93/1.50  Timing (in seconds)
% 2.93/1.50  ----------------------
% 2.93/1.50  Preprocessing        : 0.28
% 2.93/1.50  Parsing              : 0.14
% 2.93/1.50  CNF conversion       : 0.02
% 2.93/1.50  Main loop            : 0.37
% 2.93/1.50  Inferencing          : 0.15
% 2.93/1.50  Reduction            : 0.10
% 2.93/1.50  Demodulation         : 0.07
% 2.93/1.50  BG Simplification    : 0.02
% 2.93/1.50  Subsumption          : 0.08
% 2.93/1.50  Abstraction          : 0.02
% 2.93/1.50  MUC search           : 0.00
% 2.93/1.50  Cooper               : 0.00
% 2.93/1.50  Total                : 0.68
% 2.93/1.50  Index Insertion      : 0.00
% 2.93/1.50  Index Deletion       : 0.00
% 2.93/1.50  Index Matching       : 0.00
% 2.93/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
