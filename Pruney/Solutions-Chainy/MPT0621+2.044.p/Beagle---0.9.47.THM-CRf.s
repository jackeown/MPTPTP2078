%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 183 expanded)
%              Number of leaves         :   26 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 508 expanded)
%              Number of equality atoms :   98 ( 359 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    ! [A_28] : k1_tarski(A_28) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_133,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(k1_tarski(A_59),B_60) = k1_xboole_0
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_73,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | k4_xboole_0(A_42,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_143,plain,(
    ! [A_59] :
      ( k1_tarski(A_59) = k1_xboole_0
      | ~ r2_hidden(A_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_78])).

tff(c_167,plain,(
    ! [A_59] : ~ r2_hidden(A_59,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_143])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k1_tarski(A_13),B_14) = k1_xboole_0
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_188,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | k4_xboole_0(k1_tarski(A_63),k1_tarski(B_62)) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r2_hidden(A_65,k1_tarski(B_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_207,plain,(
    ! [B_64] :
      ( '#skF_1'(k1_tarski(B_64)) = B_64
      | k1_tarski(B_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_200])).

tff(c_212,plain,(
    ! [B_64] : '#skF_1'(k1_tarski(B_64)) = B_64 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_207])).

tff(c_22,plain,(
    ! [A_15,B_19] :
      ( k2_relat_1('#skF_2'(A_15,B_19)) = k1_tarski(B_19)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_15,B_19] :
      ( k1_relat_1('#skF_2'(A_15,B_19)) = A_15
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_15,B_19] :
      ( v1_funct_1('#skF_2'(A_15,B_19))
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_15,B_19] :
      ( v1_relat_1('#skF_2'(A_15,B_19))
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    ! [C_39,B_40] :
      ( C_39 = B_40
      | k1_relat_1(C_39) != '#skF_3'
      | k1_relat_1(B_40) != '#skF_3'
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_129,plain,(
    ! [B_56,A_57,B_58] :
      ( B_56 = '#skF_2'(A_57,B_58)
      | k1_relat_1('#skF_2'(A_57,B_58)) != '#skF_3'
      | k1_relat_1(B_56) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_57,B_58))
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56)
      | k1_xboole_0 = A_57 ) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_227,plain,(
    ! [B_67,A_68,B_69] :
      ( B_67 = '#skF_2'(A_68,B_69)
      | k1_relat_1('#skF_2'(A_68,B_69)) != '#skF_3'
      | k1_relat_1(B_67) != '#skF_3'
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | k1_xboole_0 = A_68 ) ),
    inference(resolution,[status(thm)],[c_26,c_129])).

tff(c_231,plain,(
    ! [B_70,A_71,B_72] :
      ( B_70 = '#skF_2'(A_71,B_72)
      | A_71 != '#skF_3'
      | k1_relat_1(B_70) != '#skF_3'
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70)
      | k1_xboole_0 = A_71
      | k1_xboole_0 = A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_227])).

tff(c_236,plain,(
    ! [A_75,B_76,A_73,B_74] :
      ( '#skF_2'(A_75,B_76) = '#skF_2'(A_73,B_74)
      | A_73 != '#skF_3'
      | k1_relat_1('#skF_2'(A_75,B_76)) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_75,B_76))
      | k1_xboole_0 = A_73
      | k1_xboole_0 = A_75 ) ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_241,plain,(
    ! [A_79,B_80,A_77,B_78] :
      ( '#skF_2'(A_79,B_80) = '#skF_2'(A_77,B_78)
      | A_77 != '#skF_3'
      | k1_relat_1('#skF_2'(A_79,B_80)) != '#skF_3'
      | k1_xboole_0 = A_77
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_26,c_236])).

tff(c_248,plain,(
    ! [A_83,B_84,A_81,B_82] :
      ( '#skF_2'(A_83,B_84) = '#skF_2'(A_81,B_82)
      | A_81 != '#skF_3'
      | A_83 != '#skF_3'
      | k1_xboole_0 = A_81
      | k1_xboole_0 = A_83
      | k1_xboole_0 = A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_241])).

tff(c_274,plain,(
    ! [A_81,B_82,B_84,A_83] :
      ( k2_relat_1('#skF_2'(A_81,B_82)) = k1_tarski(B_84)
      | k1_xboole_0 = A_83
      | A_81 != '#skF_3'
      | A_83 != '#skF_3'
      | k1_xboole_0 = A_81
      | k1_xboole_0 = A_83
      | k1_xboole_0 = A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_22])).

tff(c_377,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_30])).

tff(c_409,plain,(
    ! [A_95,B_96,B_97] :
      ( k2_relat_1('#skF_2'(A_95,B_96)) = k1_tarski(B_97)
      | A_95 != '#skF_3'
      | k1_xboole_0 = A_95 ) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_477,plain,(
    ! [B_100,A_101,B_102] :
      ( B_100 = '#skF_1'(k2_relat_1('#skF_2'(A_101,B_102)))
      | A_101 != '#skF_3'
      | k1_xboole_0 = A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_212])).

tff(c_727,plain,(
    ! [B_100,B_19,A_15] :
      ( B_100 = '#skF_1'(k1_tarski(B_19))
      | A_15 != '#skF_3'
      | k1_xboole_0 = A_15
      | k1_xboole_0 = A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_477])).

tff(c_729,plain,(
    ! [B_19,B_100,A_15] :
      ( B_19 = B_100
      | A_15 != '#skF_3'
      | k1_xboole_0 = A_15
      | k1_xboole_0 = A_15 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_727])).

tff(c_732,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_729])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_30])).

tff(c_790,plain,(
    ! [B_478] : k1_xboole_0 = B_478 ),
    inference(splitRight,[status(thm)],[c_729])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | k4_xboole_0(k1_tarski(A_51),B_52) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_121,plain,(
    ! [A_51,B_8] : r2_hidden(A_51,k2_xboole_0(k1_tarski(A_51),B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_792,plain,(
    ! [A_51] : r2_hidden(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_121])).

tff(c_1011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.41  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.78/1.41  
% 2.78/1.41  %Foreground sorts:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Background operators:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Foreground operators:
% 2.78/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.41  
% 2.78/1.43  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.78/1.43  tff(f_52, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.78/1.43  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 2.78/1.43  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.78/1.43  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.78/1.43  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.78/1.43  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.78/1.43  tff(f_69, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.78/1.43  tff(f_88, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.78/1.43  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.78/1.43  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.43  tff(c_42, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.78/1.43  tff(c_46, plain, (![A_28]: (k1_tarski(A_28)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_42])).
% 2.78/1.43  tff(c_133, plain, (![A_59, B_60]: (k4_xboole_0(k1_tarski(A_59), B_60)=k1_xboole_0 | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.43  tff(c_73, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | k4_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.43  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.43  tff(c_78, plain, (![A_42]: (k1_xboole_0=A_42 | k4_xboole_0(A_42, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_10])).
% 2.78/1.43  tff(c_143, plain, (![A_59]: (k1_tarski(A_59)=k1_xboole_0 | ~r2_hidden(A_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_133, c_78])).
% 2.78/1.43  tff(c_167, plain, (![A_59]: (~r2_hidden(A_59, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_46, c_143])).
% 2.78/1.43  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.43  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(k1_tarski(A_13), B_14)=k1_xboole_0 | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.43  tff(c_188, plain, (![B_62, A_63]: (B_62=A_63 | k4_xboole_0(k1_tarski(A_63), k1_tarski(B_62))!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.43  tff(c_200, plain, (![B_64, A_65]: (B_64=A_65 | ~r2_hidden(A_65, k1_tarski(B_64)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_188])).
% 2.78/1.43  tff(c_207, plain, (![B_64]: ('#skF_1'(k1_tarski(B_64))=B_64 | k1_tarski(B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_200])).
% 2.78/1.43  tff(c_212, plain, (![B_64]: ('#skF_1'(k1_tarski(B_64))=B_64)), inference(negUnitSimplification, [status(thm)], [c_46, c_207])).
% 2.78/1.43  tff(c_22, plain, (![A_15, B_19]: (k2_relat_1('#skF_2'(A_15, B_19))=k1_tarski(B_19) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.43  tff(c_24, plain, (![A_15, B_19]: (k1_relat_1('#skF_2'(A_15, B_19))=A_15 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.43  tff(c_26, plain, (![A_15, B_19]: (v1_funct_1('#skF_2'(A_15, B_19)) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.43  tff(c_28, plain, (![A_15, B_19]: (v1_relat_1('#skF_2'(A_15, B_19)) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.43  tff(c_68, plain, (![C_39, B_40]: (C_39=B_40 | k1_relat_1(C_39)!='#skF_3' | k1_relat_1(B_40)!='#skF_3' | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.78/1.43  tff(c_129, plain, (![B_56, A_57, B_58]: (B_56='#skF_2'(A_57, B_58) | k1_relat_1('#skF_2'(A_57, B_58))!='#skF_3' | k1_relat_1(B_56)!='#skF_3' | ~v1_funct_1('#skF_2'(A_57, B_58)) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56) | k1_xboole_0=A_57)), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.78/1.43  tff(c_227, plain, (![B_67, A_68, B_69]: (B_67='#skF_2'(A_68, B_69) | k1_relat_1('#skF_2'(A_68, B_69))!='#skF_3' | k1_relat_1(B_67)!='#skF_3' | ~v1_funct_1(B_67) | ~v1_relat_1(B_67) | k1_xboole_0=A_68)), inference(resolution, [status(thm)], [c_26, c_129])).
% 2.78/1.43  tff(c_231, plain, (![B_70, A_71, B_72]: (B_70='#skF_2'(A_71, B_72) | A_71!='#skF_3' | k1_relat_1(B_70)!='#skF_3' | ~v1_funct_1(B_70) | ~v1_relat_1(B_70) | k1_xboole_0=A_71 | k1_xboole_0=A_71)), inference(superposition, [status(thm), theory('equality')], [c_24, c_227])).
% 2.78/1.43  tff(c_236, plain, (![A_75, B_76, A_73, B_74]: ('#skF_2'(A_75, B_76)='#skF_2'(A_73, B_74) | A_73!='#skF_3' | k1_relat_1('#skF_2'(A_75, B_76))!='#skF_3' | ~v1_funct_1('#skF_2'(A_75, B_76)) | k1_xboole_0=A_73 | k1_xboole_0=A_75)), inference(resolution, [status(thm)], [c_28, c_231])).
% 2.78/1.43  tff(c_241, plain, (![A_79, B_80, A_77, B_78]: ('#skF_2'(A_79, B_80)='#skF_2'(A_77, B_78) | A_77!='#skF_3' | k1_relat_1('#skF_2'(A_79, B_80))!='#skF_3' | k1_xboole_0=A_77 | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_26, c_236])).
% 2.78/1.43  tff(c_248, plain, (![A_83, B_84, A_81, B_82]: ('#skF_2'(A_83, B_84)='#skF_2'(A_81, B_82) | A_81!='#skF_3' | A_83!='#skF_3' | k1_xboole_0=A_81 | k1_xboole_0=A_83 | k1_xboole_0=A_83)), inference(superposition, [status(thm), theory('equality')], [c_24, c_241])).
% 2.78/1.43  tff(c_274, plain, (![A_81, B_82, B_84, A_83]: (k2_relat_1('#skF_2'(A_81, B_82))=k1_tarski(B_84) | k1_xboole_0=A_83 | A_81!='#skF_3' | A_83!='#skF_3' | k1_xboole_0=A_81 | k1_xboole_0=A_83 | k1_xboole_0=A_83)), inference(superposition, [status(thm), theory('equality')], [c_248, c_22])).
% 2.78/1.43  tff(c_377, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_274])).
% 2.78/1.43  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.78/1.43  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_377, c_30])).
% 2.78/1.43  tff(c_409, plain, (![A_95, B_96, B_97]: (k2_relat_1('#skF_2'(A_95, B_96))=k1_tarski(B_97) | A_95!='#skF_3' | k1_xboole_0=A_95)), inference(splitRight, [status(thm)], [c_274])).
% 2.78/1.43  tff(c_477, plain, (![B_100, A_101, B_102]: (B_100='#skF_1'(k2_relat_1('#skF_2'(A_101, B_102))) | A_101!='#skF_3' | k1_xboole_0=A_101)), inference(superposition, [status(thm), theory('equality')], [c_409, c_212])).
% 2.78/1.43  tff(c_727, plain, (![B_100, B_19, A_15]: (B_100='#skF_1'(k1_tarski(B_19)) | A_15!='#skF_3' | k1_xboole_0=A_15 | k1_xboole_0=A_15)), inference(superposition, [status(thm), theory('equality')], [c_22, c_477])).
% 2.78/1.43  tff(c_729, plain, (![B_19, B_100, A_15]: (B_19=B_100 | A_15!='#skF_3' | k1_xboole_0=A_15 | k1_xboole_0=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_727])).
% 2.78/1.43  tff(c_732, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_729])).
% 2.78/1.43  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_732, c_30])).
% 2.78/1.43  tff(c_790, plain, (![B_478]: (k1_xboole_0=B_478)), inference(splitRight, [status(thm)], [c_729])).
% 2.78/1.43  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.43  tff(c_111, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | k4_xboole_0(k1_tarski(A_51), B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.43  tff(c_121, plain, (![A_51, B_8]: (r2_hidden(A_51, k2_xboole_0(k1_tarski(A_51), B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_111])).
% 2.78/1.43  tff(c_792, plain, (![A_51]: (r2_hidden(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_790, c_121])).
% 2.78/1.43  tff(c_1011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_792])).
% 2.78/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  Inference rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Ref     : 2
% 2.78/1.43  #Sup     : 244
% 2.78/1.43  #Fact    : 0
% 2.78/1.43  #Define  : 0
% 2.78/1.43  #Split   : 3
% 2.78/1.43  #Chain   : 0
% 2.78/1.43  #Close   : 0
% 2.78/1.43  
% 2.78/1.43  Ordering : KBO
% 2.78/1.43  
% 2.78/1.43  Simplification rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Subsume      : 72
% 2.78/1.43  #Demod        : 90
% 2.78/1.43  #Tautology    : 49
% 2.78/1.43  #SimpNegUnit  : 6
% 2.78/1.43  #BackRed      : 40
% 2.78/1.43  
% 2.78/1.43  #Partial instantiations: 495
% 2.78/1.43  #Strategies tried      : 1
% 2.78/1.43  
% 2.78/1.43  Timing (in seconds)
% 2.78/1.43  ----------------------
% 2.78/1.43  Preprocessing        : 0.29
% 2.78/1.43  Parsing              : 0.16
% 2.78/1.43  CNF conversion       : 0.02
% 2.78/1.43  Main loop            : 0.36
% 2.78/1.43  Inferencing          : 0.16
% 2.78/1.43  Reduction            : 0.09
% 2.78/1.43  Demodulation         : 0.05
% 2.78/1.43  BG Simplification    : 0.02
% 2.78/1.43  Subsumption          : 0.08
% 2.78/1.43  Abstraction          : 0.02
% 2.78/1.43  MUC search           : 0.00
% 2.78/1.43  Cooper               : 0.00
% 2.78/1.43  Total                : 0.69
% 2.78/1.43  Index Insertion      : 0.00
% 2.78/1.43  Index Deletion       : 0.00
% 2.78/1.43  Index Matching       : 0.00
% 2.78/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
