%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:02 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 164 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 430 expanded)
%              Number of equality atoms :   69 ( 230 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_69,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_498,plain,(
    ! [A_116,B_117] :
      ( r2_hidden(k4_tarski('#skF_1'(A_116,B_117),'#skF_2'(A_116,B_117)),A_116)
      | r2_hidden('#skF_3'(A_116,B_117),B_117)
      | k1_relat_1(A_116) = B_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_54,B_55] : ~ r2_hidden(A_54,k2_zfmisc_1(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_509,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_117),B_117)
      | k1_relat_1(k1_xboole_0) = B_117 ) ),
    inference(resolution,[status(thm)],[c_498,c_102])).

tff(c_514,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_117),B_117)
      | k1_xboole_0 = B_117 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_509])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_515,plain,(
    ! [B_118] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_118),B_118)
      | k1_xboole_0 = B_118 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_509])).

tff(c_30,plain,(
    ! [A_24,B_25] : v1_funct_1('#skF_5'(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_24,B_25] : k1_relat_1('#skF_5'(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_24,B_25] : v1_relat_1('#skF_5'(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_31] : v1_funct_1('#skF_6'(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    ! [A_31] : k1_relat_1('#skF_6'(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [A_31] : v1_relat_1('#skF_6'(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_73,plain,(
    ! [C_51,B_52] :
      ( C_51 = B_52
      | k1_relat_1(C_51) != '#skF_7'
      | k1_relat_1(B_52) != '#skF_7'
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_77,plain,(
    ! [B_52,A_31] :
      ( B_52 = '#skF_6'(A_31)
      | k1_relat_1('#skF_6'(A_31)) != '#skF_7'
      | k1_relat_1(B_52) != '#skF_7'
      | ~ v1_funct_1('#skF_6'(A_31))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_147,plain,(
    ! [B_69,A_70] :
      ( B_69 = '#skF_6'(A_70)
      | A_70 != '#skF_7'
      | k1_relat_1(B_69) != '#skF_7'
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_77])).

tff(c_149,plain,(
    ! [A_70,A_24,B_25] :
      ( '#skF_6'(A_70) = '#skF_5'(A_24,B_25)
      | A_70 != '#skF_7'
      | k1_relat_1('#skF_5'(A_24,B_25)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_24,B_25)) ) ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_216,plain,(
    ! [A_75,A_76,B_77] :
      ( '#skF_6'(A_75) = '#skF_5'(A_76,B_77)
      | A_75 != '#skF_7'
      | A_76 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_149])).

tff(c_26,plain,(
    ! [A_24,B_25,D_30] :
      ( k1_funct_1('#skF_5'(A_24,B_25),D_30) = B_25
      | ~ r2_hidden(D_30,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_231,plain,(
    ! [A_75,D_30,B_77,A_76] :
      ( k1_funct_1('#skF_6'(A_75),D_30) = B_77
      | ~ r2_hidden(D_30,A_76)
      | A_75 != '#skF_7'
      | A_76 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_26])).

tff(c_998,plain,(
    ! [A_75,B_118] :
      ( k1_funct_1('#skF_6'(A_75),'#skF_3'(k1_xboole_0,B_118)) = k1_xboole_0
      | A_75 != '#skF_7'
      | B_118 != '#skF_7'
      | k1_xboole_0 = B_118 ) ),
    inference(resolution,[status(thm)],[c_515,c_231])).

tff(c_726,plain,(
    ! [A_119,B_120] :
      ( k1_funct_1('#skF_6'(A_119),'#skF_3'(k1_xboole_0,B_120)) = '#skF_7'
      | A_119 != '#skF_7'
      | B_120 != '#skF_7'
      | k1_xboole_0 = B_120 ) ),
    inference(resolution,[status(thm)],[c_515,c_231])).

tff(c_34,plain,(
    ! [A_31,C_36] :
      ( k1_funct_1('#skF_6'(A_31),C_36) = np__1
      | ~ r2_hidden(C_36,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_729,plain,(
    ! [B_120,A_119] :
      ( np__1 = '#skF_7'
      | ~ r2_hidden('#skF_3'(k1_xboole_0,B_120),A_119)
      | A_119 != '#skF_7'
      | B_120 != '#skF_7'
      | k1_xboole_0 = B_120 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_34])).

tff(c_898,plain,(
    np__1 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_729])).

tff(c_928,plain,(
    ! [A_918,C_919] :
      ( k1_funct_1('#skF_6'(A_918),C_919) = '#skF_7'
      | ~ r2_hidden(C_919,A_918) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_34])).

tff(c_1001,plain,(
    ! [B_118,A_75] :
      ( k1_xboole_0 = '#skF_7'
      | ~ r2_hidden('#skF_3'(k1_xboole_0,B_118),A_75)
      | A_75 != '#skF_7'
      | B_118 != '#skF_7'
      | k1_xboole_0 = B_118 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_928])).

tff(c_1028,plain,(
    ! [B_940,A_941] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_940),A_941)
      | A_941 != '#skF_7'
      | B_940 != '#skF_7'
      | k1_xboole_0 = B_940 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1001])).

tff(c_1041,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_514,c_1028])).

tff(c_1053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_42])).

tff(c_1122,plain,(
    ! [B_1028,A_1029] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_1028),A_1029)
      | A_1029 != '#skF_7'
      | B_1028 != '#skF_7'
      | k1_xboole_0 = B_1028 ) ),
    inference(splitRight,[status(thm)],[c_729])).

tff(c_1135,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_514,c_1122])).

tff(c_1147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.58  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6
% 3.16/1.58  
% 3.16/1.58  %Foreground sorts:
% 3.16/1.58  
% 3.16/1.58  
% 3.16/1.58  %Background operators:
% 3.16/1.58  
% 3.16/1.58  
% 3.16/1.58  %Foreground operators:
% 3.16/1.58  tff(np__1, type, np__1: $i).
% 3.16/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.16/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.16/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.16/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.16/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.58  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.16/1.58  
% 3.16/1.59  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.16/1.59  tff(f_42, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.16/1.59  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.16/1.59  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.16/1.59  tff(f_88, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 3.16/1.59  tff(f_57, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.16/1.59  tff(f_69, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 3.16/1.59  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.59  tff(c_498, plain, (![A_116, B_117]: (r2_hidden(k4_tarski('#skF_1'(A_116, B_117), '#skF_2'(A_116, B_117)), A_116) | r2_hidden('#skF_3'(A_116, B_117), B_117) | k1_relat_1(A_116)=B_117)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.16/1.59  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.59  tff(c_99, plain, (![A_54, B_55]: (~r2_hidden(A_54, k2_zfmisc_1(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.59  tff(c_102, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_99])).
% 3.16/1.59  tff(c_509, plain, (![B_117]: (r2_hidden('#skF_3'(k1_xboole_0, B_117), B_117) | k1_relat_1(k1_xboole_0)=B_117)), inference(resolution, [status(thm)], [c_498, c_102])).
% 3.16/1.59  tff(c_514, plain, (![B_117]: (r2_hidden('#skF_3'(k1_xboole_0, B_117), B_117) | k1_xboole_0=B_117)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_509])).
% 3.16/1.59  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.59  tff(c_515, plain, (![B_118]: (r2_hidden('#skF_3'(k1_xboole_0, B_118), B_118) | k1_xboole_0=B_118)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_509])).
% 3.16/1.59  tff(c_30, plain, (![A_24, B_25]: (v1_funct_1('#skF_5'(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.59  tff(c_28, plain, (![A_24, B_25]: (k1_relat_1('#skF_5'(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.59  tff(c_32, plain, (![A_24, B_25]: (v1_relat_1('#skF_5'(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.59  tff(c_38, plain, (![A_31]: (v1_funct_1('#skF_6'(A_31)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.59  tff(c_36, plain, (![A_31]: (k1_relat_1('#skF_6'(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.59  tff(c_40, plain, (![A_31]: (v1_relat_1('#skF_6'(A_31)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.59  tff(c_73, plain, (![C_51, B_52]: (C_51=B_52 | k1_relat_1(C_51)!='#skF_7' | k1_relat_1(B_52)!='#skF_7' | ~v1_funct_1(C_51) | ~v1_relat_1(C_51) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.59  tff(c_77, plain, (![B_52, A_31]: (B_52='#skF_6'(A_31) | k1_relat_1('#skF_6'(A_31))!='#skF_7' | k1_relat_1(B_52)!='#skF_7' | ~v1_funct_1('#skF_6'(A_31)) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_40, c_73])).
% 3.16/1.59  tff(c_147, plain, (![B_69, A_70]: (B_69='#skF_6'(A_70) | A_70!='#skF_7' | k1_relat_1(B_69)!='#skF_7' | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_77])).
% 3.16/1.59  tff(c_149, plain, (![A_70, A_24, B_25]: ('#skF_6'(A_70)='#skF_5'(A_24, B_25) | A_70!='#skF_7' | k1_relat_1('#skF_5'(A_24, B_25))!='#skF_7' | ~v1_funct_1('#skF_5'(A_24, B_25)))), inference(resolution, [status(thm)], [c_32, c_147])).
% 3.16/1.59  tff(c_216, plain, (![A_75, A_76, B_77]: ('#skF_6'(A_75)='#skF_5'(A_76, B_77) | A_75!='#skF_7' | A_76!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_149])).
% 3.16/1.59  tff(c_26, plain, (![A_24, B_25, D_30]: (k1_funct_1('#skF_5'(A_24, B_25), D_30)=B_25 | ~r2_hidden(D_30, A_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.59  tff(c_231, plain, (![A_75, D_30, B_77, A_76]: (k1_funct_1('#skF_6'(A_75), D_30)=B_77 | ~r2_hidden(D_30, A_76) | A_75!='#skF_7' | A_76!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_216, c_26])).
% 3.16/1.59  tff(c_998, plain, (![A_75, B_118]: (k1_funct_1('#skF_6'(A_75), '#skF_3'(k1_xboole_0, B_118))=k1_xboole_0 | A_75!='#skF_7' | B_118!='#skF_7' | k1_xboole_0=B_118)), inference(resolution, [status(thm)], [c_515, c_231])).
% 3.16/1.59  tff(c_726, plain, (![A_119, B_120]: (k1_funct_1('#skF_6'(A_119), '#skF_3'(k1_xboole_0, B_120))='#skF_7' | A_119!='#skF_7' | B_120!='#skF_7' | k1_xboole_0=B_120)), inference(resolution, [status(thm)], [c_515, c_231])).
% 3.16/1.59  tff(c_34, plain, (![A_31, C_36]: (k1_funct_1('#skF_6'(A_31), C_36)=np__1 | ~r2_hidden(C_36, A_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.59  tff(c_729, plain, (![B_120, A_119]: (np__1='#skF_7' | ~r2_hidden('#skF_3'(k1_xboole_0, B_120), A_119) | A_119!='#skF_7' | B_120!='#skF_7' | k1_xboole_0=B_120)), inference(superposition, [status(thm), theory('equality')], [c_726, c_34])).
% 3.16/1.59  tff(c_898, plain, (np__1='#skF_7'), inference(splitLeft, [status(thm)], [c_729])).
% 3.16/1.59  tff(c_928, plain, (![A_918, C_919]: (k1_funct_1('#skF_6'(A_918), C_919)='#skF_7' | ~r2_hidden(C_919, A_918))), inference(demodulation, [status(thm), theory('equality')], [c_898, c_34])).
% 3.16/1.59  tff(c_1001, plain, (![B_118, A_75]: (k1_xboole_0='#skF_7' | ~r2_hidden('#skF_3'(k1_xboole_0, B_118), A_75) | A_75!='#skF_7' | B_118!='#skF_7' | k1_xboole_0=B_118)), inference(superposition, [status(thm), theory('equality')], [c_998, c_928])).
% 3.16/1.59  tff(c_1028, plain, (![B_940, A_941]: (~r2_hidden('#skF_3'(k1_xboole_0, B_940), A_941) | A_941!='#skF_7' | B_940!='#skF_7' | k1_xboole_0=B_940)), inference(negUnitSimplification, [status(thm)], [c_42, c_1001])).
% 3.16/1.59  tff(c_1041, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_514, c_1028])).
% 3.16/1.59  tff(c_1053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1041, c_42])).
% 3.16/1.59  tff(c_1122, plain, (![B_1028, A_1029]: (~r2_hidden('#skF_3'(k1_xboole_0, B_1028), A_1029) | A_1029!='#skF_7' | B_1028!='#skF_7' | k1_xboole_0=B_1028)), inference(splitRight, [status(thm)], [c_729])).
% 3.16/1.59  tff(c_1135, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_514, c_1122])).
% 3.16/1.59  tff(c_1147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1135, c_42])).
% 3.16/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.59  
% 3.16/1.59  Inference rules
% 3.16/1.59  ----------------------
% 3.16/1.59  #Ref     : 1
% 3.16/1.59  #Sup     : 281
% 3.16/1.59  #Fact    : 0
% 3.16/1.59  #Define  : 0
% 3.16/1.59  #Split   : 1
% 3.16/1.59  #Chain   : 0
% 3.16/1.59  #Close   : 0
% 3.16/1.59  
% 3.16/1.59  Ordering : KBO
% 3.16/1.59  
% 3.16/1.59  Simplification rules
% 3.16/1.59  ----------------------
% 3.16/1.59  #Subsume      : 66
% 3.16/1.59  #Demod        : 84
% 3.16/1.59  #Tautology    : 49
% 3.16/1.59  #SimpNegUnit  : 2
% 3.16/1.59  #BackRed      : 17
% 3.16/1.59  
% 3.16/1.59  #Partial instantiations: 616
% 3.16/1.59  #Strategies tried      : 1
% 3.16/1.59  
% 3.16/1.59  Timing (in seconds)
% 3.16/1.59  ----------------------
% 3.16/1.59  Preprocessing        : 0.33
% 3.16/1.59  Parsing              : 0.17
% 3.16/1.59  CNF conversion       : 0.03
% 3.16/1.59  Main loop            : 0.42
% 3.16/1.59  Inferencing          : 0.16
% 3.16/1.59  Reduction            : 0.12
% 3.16/1.59  Demodulation         : 0.08
% 3.16/1.59  BG Simplification    : 0.02
% 3.16/1.59  Subsumption          : 0.09
% 3.16/1.59  Abstraction          : 0.02
% 3.16/1.59  MUC search           : 0.00
% 3.16/1.59  Cooper               : 0.00
% 3.16/1.59  Total                : 0.78
% 3.16/1.59  Index Insertion      : 0.00
% 3.16/1.59  Index Deletion       : 0.00
% 3.16/1.59  Index Matching       : 0.00
% 3.16/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
