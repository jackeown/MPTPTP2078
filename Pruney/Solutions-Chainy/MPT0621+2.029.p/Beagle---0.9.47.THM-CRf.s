%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:02 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 160 expanded)
%              Number of equality atoms :   54 (  84 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_88,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_69,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_584,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_hidden('#skF_1'(A_108,B_109,C_110),B_109)
      | r2_hidden('#skF_2'(A_108,B_109,C_110),C_110)
      | k3_xboole_0(A_108,B_109) = C_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [A_43,B_44] : ~ r2_hidden(A_43,k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_604,plain,(
    ! [A_108,C_110] :
      ( r2_hidden('#skF_2'(A_108,k1_xboole_0,C_110),C_110)
      | k3_xboole_0(A_108,k1_xboole_0) = C_110 ) ),
    inference(resolution,[status(thm)],[c_584,c_105])).

tff(c_625,plain,(
    ! [A_108,C_110] :
      ( r2_hidden('#skF_2'(A_108,k1_xboole_0,C_110),C_110)
      | k1_xboole_0 = C_110 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_604])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_630,plain,(
    ! [A_111,C_112] :
      ( r2_hidden('#skF_2'(A_111,k1_xboole_0,C_112),C_112)
      | k1_xboole_0 = C_112 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_604])).

tff(c_34,plain,(
    ! [A_12,B_13] : v1_funct_1('#skF_3'(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_12,B_13] : k1_relat_1('#skF_3'(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_12,B_13] : v1_relat_1('#skF_3'(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,(
    ! [A_19] : v1_funct_1('#skF_4'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [A_19] : k1_relat_1('#skF_4'(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [A_19] : v1_relat_1('#skF_4'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_91,plain,(
    ! [C_41,B_42] :
      ( C_41 = B_42
      | k1_relat_1(C_41) != '#skF_5'
      | k1_relat_1(B_42) != '#skF_5'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

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
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,(
    ! [A_67,D_18,B_69,A_68] :
      ( k1_funct_1('#skF_4'(A_67),D_18) = B_69
      | ~ r2_hidden(D_18,A_68)
      | A_67 != '#skF_5'
      | A_68 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_30])).

tff(c_864,plain,(
    ! [A_118,A_119,C_120] :
      ( k1_funct_1('#skF_4'(A_118),'#skF_2'(A_119,k1_xboole_0,C_120)) = '#skF_5'
      | A_118 != '#skF_5'
      | C_120 != '#skF_5'
      | k1_xboole_0 = C_120 ) ),
    inference(resolution,[status(thm)],[c_630,c_242])).

tff(c_38,plain,(
    ! [A_19,C_24] :
      ( k1_funct_1('#skF_4'(A_19),C_24) = k1_xboole_0
      | ~ r2_hidden(C_24,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_867,plain,(
    ! [A_119,C_120,A_118] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_119,k1_xboole_0,C_120),A_118)
      | A_118 != '#skF_5'
      | C_120 != '#skF_5'
      | k1_xboole_0 = C_120 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_38])).

tff(c_1040,plain,(
    ! [A_810,C_811,A_812] :
      ( ~ r2_hidden('#skF_2'(A_810,k1_xboole_0,C_811),A_812)
      | A_812 != '#skF_5'
      | C_811 != '#skF_5'
      | k1_xboole_0 = C_811 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_867])).

tff(c_1100,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_625,c_1040])).

tff(c_1118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.45  
% 2.82/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.45  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 2.82/1.45  
% 2.82/1.45  %Foreground sorts:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Background operators:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Foreground operators:
% 2.82/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.82/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.45  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.82/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.45  
% 3.20/1.47  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.20/1.47  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.20/1.47  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.20/1.47  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.20/1.47  tff(f_88, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 3.20/1.47  tff(f_57, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.20/1.47  tff(f_69, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.20/1.47  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.47  tff(c_584, plain, (![A_108, B_109, C_110]: (r2_hidden('#skF_1'(A_108, B_109, C_110), B_109) | r2_hidden('#skF_2'(A_108, B_109, C_110), C_110) | k3_xboole_0(A_108, B_109)=C_110)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.20/1.47  tff(c_24, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.47  tff(c_102, plain, (![A_43, B_44]: (~r2_hidden(A_43, k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.47  tff(c_105, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_102])).
% 3.20/1.47  tff(c_604, plain, (![A_108, C_110]: (r2_hidden('#skF_2'(A_108, k1_xboole_0, C_110), C_110) | k3_xboole_0(A_108, k1_xboole_0)=C_110)), inference(resolution, [status(thm)], [c_584, c_105])).
% 3.20/1.47  tff(c_625, plain, (![A_108, C_110]: (r2_hidden('#skF_2'(A_108, k1_xboole_0, C_110), C_110) | k1_xboole_0=C_110)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_604])).
% 3.20/1.47  tff(c_46, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.47  tff(c_630, plain, (![A_111, C_112]: (r2_hidden('#skF_2'(A_111, k1_xboole_0, C_112), C_112) | k1_xboole_0=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_604])).
% 3.20/1.47  tff(c_34, plain, (![A_12, B_13]: (v1_funct_1('#skF_3'(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.47  tff(c_32, plain, (![A_12, B_13]: (k1_relat_1('#skF_3'(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.47  tff(c_36, plain, (![A_12, B_13]: (v1_relat_1('#skF_3'(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.47  tff(c_42, plain, (![A_19]: (v1_funct_1('#skF_4'(A_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.47  tff(c_40, plain, (![A_19]: (k1_relat_1('#skF_4'(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.47  tff(c_44, plain, (![A_19]: (v1_relat_1('#skF_4'(A_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.47  tff(c_91, plain, (![C_41, B_42]: (C_41=B_42 | k1_relat_1(C_41)!='#skF_5' | k1_relat_1(B_42)!='#skF_5' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.47  tff(c_95, plain, (![B_42, A_19]: (B_42='#skF_4'(A_19) | k1_relat_1('#skF_4'(A_19))!='#skF_5' | k1_relat_1(B_42)!='#skF_5' | ~v1_funct_1('#skF_4'(A_19)) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_44, c_91])).
% 3.20/1.47  tff(c_158, plain, (![B_61, A_62]: (B_61='#skF_4'(A_62) | A_62!='#skF_5' | k1_relat_1(B_61)!='#skF_5' | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_95])).
% 3.20/1.47  tff(c_160, plain, (![A_62, A_12, B_13]: ('#skF_4'(A_62)='#skF_3'(A_12, B_13) | A_62!='#skF_5' | k1_relat_1('#skF_3'(A_12, B_13))!='#skF_5' | ~v1_funct_1('#skF_3'(A_12, B_13)))), inference(resolution, [status(thm)], [c_36, c_158])).
% 3.20/1.47  tff(c_227, plain, (![A_67, A_68, B_69]: ('#skF_4'(A_67)='#skF_3'(A_68, B_69) | A_67!='#skF_5' | A_68!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_160])).
% 3.20/1.47  tff(c_30, plain, (![A_12, B_13, D_18]: (k1_funct_1('#skF_3'(A_12, B_13), D_18)=B_13 | ~r2_hidden(D_18, A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.47  tff(c_242, plain, (![A_67, D_18, B_69, A_68]: (k1_funct_1('#skF_4'(A_67), D_18)=B_69 | ~r2_hidden(D_18, A_68) | A_67!='#skF_5' | A_68!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_227, c_30])).
% 3.20/1.47  tff(c_864, plain, (![A_118, A_119, C_120]: (k1_funct_1('#skF_4'(A_118), '#skF_2'(A_119, k1_xboole_0, C_120))='#skF_5' | A_118!='#skF_5' | C_120!='#skF_5' | k1_xboole_0=C_120)), inference(resolution, [status(thm)], [c_630, c_242])).
% 3.20/1.47  tff(c_38, plain, (![A_19, C_24]: (k1_funct_1('#skF_4'(A_19), C_24)=k1_xboole_0 | ~r2_hidden(C_24, A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.47  tff(c_867, plain, (![A_119, C_120, A_118]: (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_2'(A_119, k1_xboole_0, C_120), A_118) | A_118!='#skF_5' | C_120!='#skF_5' | k1_xboole_0=C_120)), inference(superposition, [status(thm), theory('equality')], [c_864, c_38])).
% 3.20/1.47  tff(c_1040, plain, (![A_810, C_811, A_812]: (~r2_hidden('#skF_2'(A_810, k1_xboole_0, C_811), A_812) | A_812!='#skF_5' | C_811!='#skF_5' | k1_xboole_0=C_811)), inference(negUnitSimplification, [status(thm)], [c_46, c_867])).
% 3.20/1.47  tff(c_1100, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_625, c_1040])).
% 3.20/1.47  tff(c_1118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1100, c_46])).
% 3.20/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  Inference rules
% 3.20/1.47  ----------------------
% 3.20/1.47  #Ref     : 1
% 3.20/1.47  #Sup     : 260
% 3.20/1.47  #Fact    : 0
% 3.20/1.47  #Define  : 0
% 3.20/1.47  #Split   : 0
% 3.20/1.47  #Chain   : 0
% 3.20/1.47  #Close   : 0
% 3.20/1.47  
% 3.20/1.47  Ordering : KBO
% 3.20/1.47  
% 3.20/1.47  Simplification rules
% 3.20/1.47  ----------------------
% 3.20/1.47  #Subsume      : 66
% 3.20/1.47  #Demod        : 82
% 3.20/1.47  #Tautology    : 56
% 3.20/1.47  #SimpNegUnit  : 10
% 3.20/1.47  #BackRed      : 15
% 3.20/1.47  
% 3.20/1.47  #Partial instantiations: 420
% 3.20/1.47  #Strategies tried      : 1
% 3.20/1.47  
% 3.20/1.47  Timing (in seconds)
% 3.20/1.47  ----------------------
% 3.20/1.47  Preprocessing        : 0.30
% 3.20/1.47  Parsing              : 0.15
% 3.20/1.47  CNF conversion       : 0.02
% 3.20/1.47  Main loop            : 0.41
% 3.20/1.47  Inferencing          : 0.16
% 3.20/1.47  Reduction            : 0.11
% 3.20/1.47  Demodulation         : 0.08
% 3.20/1.47  BG Simplification    : 0.02
% 3.20/1.47  Subsumption          : 0.09
% 3.20/1.47  Abstraction          : 0.02
% 3.20/1.47  MUC search           : 0.00
% 3.20/1.47  Cooper               : 0.00
% 3.20/1.47  Total                : 0.74
% 3.20/1.47  Index Insertion      : 0.00
% 3.20/1.47  Index Deletion       : 0.00
% 3.20/1.47  Index Matching       : 0.00
% 3.20/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
