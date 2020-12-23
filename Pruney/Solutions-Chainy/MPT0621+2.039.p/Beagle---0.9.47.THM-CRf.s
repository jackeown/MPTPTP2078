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
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 299 expanded)
%              Number of leaves         :   20 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 (1035 expanded)
%              Number of equality atoms :   83 ( 563 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

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
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_5,B_6] : v1_funct_1('#skF_3'(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_5,B_6] : k1_relat_1('#skF_3'(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [A_5,B_6] : v1_relat_1('#skF_3'(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_12] : v1_funct_1('#skF_4'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_12] : k1_relat_1('#skF_4'(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_12] : v1_relat_1('#skF_4'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_75,plain,(
    ! [C_35,B_36] :
      ( C_35 = B_36
      | k1_relat_1(C_35) != '#skF_5'
      | k1_relat_1(B_36) != '#skF_5'
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    ! [B_36,A_12] :
      ( B_36 = '#skF_4'(A_12)
      | k1_relat_1('#skF_4'(A_12)) != '#skF_5'
      | k1_relat_1(B_36) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_12))
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_214,plain,(
    ! [B_60,A_61] :
      ( B_60 = '#skF_4'(A_61)
      | A_61 != '#skF_5'
      | k1_relat_1(B_60) != '#skF_5'
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_79])).

tff(c_218,plain,(
    ! [A_61,A_5,B_6] :
      ( '#skF_4'(A_61) = '#skF_3'(A_5,B_6)
      | A_61 != '#skF_5'
      | k1_relat_1('#skF_3'(A_5,B_6)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_20,c_214])).

tff(c_306,plain,(
    ! [A_66,A_67,B_68] :
      ( '#skF_4'(A_66) = '#skF_3'(A_67,B_68)
      | A_66 != '#skF_5'
      | A_67 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_218])).

tff(c_14,plain,(
    ! [A_5,B_6,D_11] :
      ( k1_funct_1('#skF_3'(A_5,B_6),D_11) = B_6
      | ~ r2_hidden(D_11,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_535,plain,(
    ! [A_84,D_85,B_86,A_87] :
      ( k1_funct_1('#skF_4'(A_84),D_85) = B_86
      | ~ r2_hidden(D_85,A_87)
      | A_84 != '#skF_5'
      | A_87 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_14])).

tff(c_2435,plain,(
    ! [A_2168,A_2169,B_2170] :
      ( k1_funct_1('#skF_4'(A_2168),'#skF_2'(A_2169,B_2170)) = '#skF_5'
      | A_2168 != '#skF_5'
      | A_2169 != '#skF_5'
      | r2_hidden('#skF_1'(A_2169,B_2170),B_2170)
      | B_2170 = A_2169 ) ),
    inference(resolution,[status(thm)],[c_8,c_535])).

tff(c_22,plain,(
    ! [A_12,C_17] :
      ( k1_funct_1('#skF_4'(A_12),C_17) = k1_xboole_0
      | ~ r2_hidden(C_17,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2438,plain,(
    ! [A_2169,B_2170,A_2168] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_2169,B_2170),A_2168)
      | A_2168 != '#skF_5'
      | A_2169 != '#skF_5'
      | r2_hidden('#skF_1'(A_2169,B_2170),B_2170)
      | B_2170 = A_2169 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2435,c_22])).

tff(c_3415,plain,(
    ! [A_3018,B_3019,A_3020] :
      ( ~ r2_hidden('#skF_2'(A_3018,B_3019),A_3020)
      | A_3020 != '#skF_5'
      | A_3018 != '#skF_5'
      | r2_hidden('#skF_1'(A_3018,B_3019),B_3019)
      | B_3019 = A_3018 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2438])).

tff(c_3451,plain,(
    ! [A_3076,B_3077] :
      ( A_3076 != '#skF_5'
      | r2_hidden('#skF_1'(A_3076,B_3077),B_3077)
      | B_3077 = A_3076 ) ),
    inference(resolution,[status(thm)],[c_8,c_3415])).

tff(c_64,plain,(
    ! [A_34] :
      ( k1_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,(
    ! [A_5,B_6] :
      ( k1_relat_1('#skF_3'(A_5,B_6)) != k1_xboole_0
      | '#skF_3'(A_5,B_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_72,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 != A_5
      | '#skF_3'(A_5,B_6) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_67])).

tff(c_191,plain,(
    ! [A_46,B_47,D_48] :
      ( k1_funct_1('#skF_3'(A_46,B_47),D_48) = B_47
      | ~ r2_hidden(D_48,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_200,plain,(
    ! [D_48,B_6,A_5] :
      ( k1_funct_1(k1_xboole_0,D_48) = B_6
      | ~ r2_hidden(D_48,A_5)
      | k1_xboole_0 != A_5 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_191])).

tff(c_3500,plain,(
    ! [A_3122,B_3123] :
      ( k1_funct_1(k1_xboole_0,'#skF_1'(A_3122,B_3123)) = k1_xboole_0
      | k1_xboole_0 != B_3123
      | A_3122 != '#skF_5'
      | B_3123 = A_3122 ) ),
    inference(resolution,[status(thm)],[c_3451,c_200])).

tff(c_3481,plain,(
    ! [A_3076,B_3077,B_6] :
      ( k1_funct_1(k1_xboole_0,'#skF_1'(A_3076,B_3077)) = B_6
      | k1_xboole_0 != B_3077
      | A_3076 != '#skF_5'
      | B_3077 = A_3076 ) ),
    inference(resolution,[status(thm)],[c_3451,c_200])).

tff(c_3503,plain,(
    ! [B_6,B_3123,A_3122] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 != B_3123
      | A_3122 != '#skF_5'
      | B_3123 = A_3122
      | k1_xboole_0 != B_3123
      | A_3122 != '#skF_5'
      | B_3123 = A_3122 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3500,c_3481])).

tff(c_5652,plain,(
    ! [B_3123,A_3122] :
      ( k1_xboole_0 != B_3123
      | A_3122 != '#skF_5'
      | B_3123 = A_3122
      | k1_xboole_0 != B_3123
      | A_3122 != '#skF_5'
      | B_3123 = A_3122 ) ),
    inference(splitLeft,[status(thm)],[c_3503])).

tff(c_5659,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5652])).

tff(c_5698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5659,c_30])).

tff(c_5701,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3503])).

tff(c_5699,plain,(
    ! [B_6] : k1_xboole_0 = B_6 ),
    inference(splitRight,[status(thm)],[c_3503])).

tff(c_5976,plain,(
    ! [B_5462] : B_5462 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5701,c_5699])).

tff(c_6203,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5976,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.17  
% 5.91/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 5.91/2.17  
% 5.91/2.17  %Foreground sorts:
% 5.91/2.17  
% 5.91/2.17  
% 5.91/2.17  %Background operators:
% 5.91/2.17  
% 5.91/2.17  
% 5.91/2.17  %Foreground operators:
% 5.91/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.91/2.17  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.91/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.91/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.91/2.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.91/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.91/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.91/2.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.91/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.91/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.91/2.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.91/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.91/2.17  
% 5.91/2.18  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.91/2.18  tff(f_83, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 5.91/2.18  tff(f_52, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 5.91/2.18  tff(f_64, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 5.91/2.18  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.91/2.18  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.18  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.91/2.18  tff(c_18, plain, (![A_5, B_6]: (v1_funct_1('#skF_3'(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.91/2.18  tff(c_16, plain, (![A_5, B_6]: (k1_relat_1('#skF_3'(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.91/2.18  tff(c_20, plain, (![A_5, B_6]: (v1_relat_1('#skF_3'(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.91/2.18  tff(c_26, plain, (![A_12]: (v1_funct_1('#skF_4'(A_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.91/2.18  tff(c_24, plain, (![A_12]: (k1_relat_1('#skF_4'(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.91/2.18  tff(c_28, plain, (![A_12]: (v1_relat_1('#skF_4'(A_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.91/2.18  tff(c_75, plain, (![C_35, B_36]: (C_35=B_36 | k1_relat_1(C_35)!='#skF_5' | k1_relat_1(B_36)!='#skF_5' | ~v1_funct_1(C_35) | ~v1_relat_1(C_35) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.91/2.18  tff(c_79, plain, (![B_36, A_12]: (B_36='#skF_4'(A_12) | k1_relat_1('#skF_4'(A_12))!='#skF_5' | k1_relat_1(B_36)!='#skF_5' | ~v1_funct_1('#skF_4'(A_12)) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_28, c_75])).
% 5.91/2.18  tff(c_214, plain, (![B_60, A_61]: (B_60='#skF_4'(A_61) | A_61!='#skF_5' | k1_relat_1(B_60)!='#skF_5' | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_79])).
% 5.91/2.18  tff(c_218, plain, (![A_61, A_5, B_6]: ('#skF_4'(A_61)='#skF_3'(A_5, B_6) | A_61!='#skF_5' | k1_relat_1('#skF_3'(A_5, B_6))!='#skF_5' | ~v1_funct_1('#skF_3'(A_5, B_6)))), inference(resolution, [status(thm)], [c_20, c_214])).
% 5.91/2.18  tff(c_306, plain, (![A_66, A_67, B_68]: ('#skF_4'(A_66)='#skF_3'(A_67, B_68) | A_66!='#skF_5' | A_67!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_218])).
% 5.91/2.18  tff(c_14, plain, (![A_5, B_6, D_11]: (k1_funct_1('#skF_3'(A_5, B_6), D_11)=B_6 | ~r2_hidden(D_11, A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.91/2.18  tff(c_535, plain, (![A_84, D_85, B_86, A_87]: (k1_funct_1('#skF_4'(A_84), D_85)=B_86 | ~r2_hidden(D_85, A_87) | A_84!='#skF_5' | A_87!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_306, c_14])).
% 5.91/2.18  tff(c_2435, plain, (![A_2168, A_2169, B_2170]: (k1_funct_1('#skF_4'(A_2168), '#skF_2'(A_2169, B_2170))='#skF_5' | A_2168!='#skF_5' | A_2169!='#skF_5' | r2_hidden('#skF_1'(A_2169, B_2170), B_2170) | B_2170=A_2169)), inference(resolution, [status(thm)], [c_8, c_535])).
% 5.91/2.18  tff(c_22, plain, (![A_12, C_17]: (k1_funct_1('#skF_4'(A_12), C_17)=k1_xboole_0 | ~r2_hidden(C_17, A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.91/2.18  tff(c_2438, plain, (![A_2169, B_2170, A_2168]: (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_2'(A_2169, B_2170), A_2168) | A_2168!='#skF_5' | A_2169!='#skF_5' | r2_hidden('#skF_1'(A_2169, B_2170), B_2170) | B_2170=A_2169)), inference(superposition, [status(thm), theory('equality')], [c_2435, c_22])).
% 5.91/2.18  tff(c_3415, plain, (![A_3018, B_3019, A_3020]: (~r2_hidden('#skF_2'(A_3018, B_3019), A_3020) | A_3020!='#skF_5' | A_3018!='#skF_5' | r2_hidden('#skF_1'(A_3018, B_3019), B_3019) | B_3019=A_3018)), inference(negUnitSimplification, [status(thm)], [c_30, c_2438])).
% 5.91/2.18  tff(c_3451, plain, (![A_3076, B_3077]: (A_3076!='#skF_5' | r2_hidden('#skF_1'(A_3076, B_3077), B_3077) | B_3077=A_3076)), inference(resolution, [status(thm)], [c_8, c_3415])).
% 5.91/2.18  tff(c_64, plain, (![A_34]: (k1_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.91/2.18  tff(c_67, plain, (![A_5, B_6]: (k1_relat_1('#skF_3'(A_5, B_6))!=k1_xboole_0 | '#skF_3'(A_5, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_64])).
% 5.91/2.18  tff(c_72, plain, (![A_5, B_6]: (k1_xboole_0!=A_5 | '#skF_3'(A_5, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_67])).
% 5.91/2.18  tff(c_191, plain, (![A_46, B_47, D_48]: (k1_funct_1('#skF_3'(A_46, B_47), D_48)=B_47 | ~r2_hidden(D_48, A_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.91/2.18  tff(c_200, plain, (![D_48, B_6, A_5]: (k1_funct_1(k1_xboole_0, D_48)=B_6 | ~r2_hidden(D_48, A_5) | k1_xboole_0!=A_5)), inference(superposition, [status(thm), theory('equality')], [c_72, c_191])).
% 5.91/2.18  tff(c_3500, plain, (![A_3122, B_3123]: (k1_funct_1(k1_xboole_0, '#skF_1'(A_3122, B_3123))=k1_xboole_0 | k1_xboole_0!=B_3123 | A_3122!='#skF_5' | B_3123=A_3122)), inference(resolution, [status(thm)], [c_3451, c_200])).
% 5.91/2.18  tff(c_3481, plain, (![A_3076, B_3077, B_6]: (k1_funct_1(k1_xboole_0, '#skF_1'(A_3076, B_3077))=B_6 | k1_xboole_0!=B_3077 | A_3076!='#skF_5' | B_3077=A_3076)), inference(resolution, [status(thm)], [c_3451, c_200])).
% 5.91/2.18  tff(c_3503, plain, (![B_6, B_3123, A_3122]: (k1_xboole_0=B_6 | k1_xboole_0!=B_3123 | A_3122!='#skF_5' | B_3123=A_3122 | k1_xboole_0!=B_3123 | A_3122!='#skF_5' | B_3123=A_3122)), inference(superposition, [status(thm), theory('equality')], [c_3500, c_3481])).
% 5.91/2.18  tff(c_5652, plain, (![B_3123, A_3122]: (k1_xboole_0!=B_3123 | A_3122!='#skF_5' | B_3123=A_3122 | k1_xboole_0!=B_3123 | A_3122!='#skF_5' | B_3123=A_3122)), inference(splitLeft, [status(thm)], [c_3503])).
% 5.91/2.18  tff(c_5659, plain, (k1_xboole_0='#skF_5'), inference(reflexivity, [status(thm), theory('equality')], [c_5652])).
% 5.91/2.18  tff(c_5698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5659, c_30])).
% 5.91/2.18  tff(c_5701, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3503])).
% 5.91/2.18  tff(c_5699, plain, (![B_6]: (k1_xboole_0=B_6)), inference(splitRight, [status(thm)], [c_3503])).
% 5.91/2.18  tff(c_5976, plain, (![B_5462]: (B_5462='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5701, c_5699])).
% 5.91/2.18  tff(c_6203, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5976, c_30])).
% 5.91/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.18  
% 5.91/2.18  Inference rules
% 5.91/2.18  ----------------------
% 5.91/2.18  #Ref     : 8
% 5.91/2.18  #Sup     : 1620
% 5.91/2.18  #Fact    : 0
% 5.91/2.18  #Define  : 0
% 5.91/2.18  #Split   : 8
% 5.91/2.18  #Chain   : 0
% 5.91/2.18  #Close   : 0
% 5.91/2.18  
% 5.91/2.18  Ordering : KBO
% 5.91/2.18  
% 5.91/2.18  Simplification rules
% 5.91/2.18  ----------------------
% 5.91/2.18  #Subsume      : 429
% 5.91/2.18  #Demod        : 237
% 5.91/2.18  #Tautology    : 137
% 5.91/2.18  #SimpNegUnit  : 8
% 5.91/2.18  #BackRed      : 38
% 5.91/2.18  
% 5.91/2.18  #Partial instantiations: 3951
% 5.91/2.18  #Strategies tried      : 1
% 5.91/2.18  
% 5.91/2.18  Timing (in seconds)
% 5.91/2.18  ----------------------
% 5.91/2.19  Preprocessing        : 0.29
% 5.91/2.19  Parsing              : 0.15
% 5.91/2.19  CNF conversion       : 0.02
% 5.91/2.19  Main loop            : 1.15
% 5.91/2.19  Inferencing          : 0.40
% 5.91/2.19  Reduction            : 0.31
% 5.91/2.19  Demodulation         : 0.21
% 5.91/2.19  BG Simplification    : 0.06
% 5.91/2.19  Subsumption          : 0.31
% 5.91/2.19  Abstraction          : 0.05
% 5.91/2.19  MUC search           : 0.00
% 5.91/2.19  Cooper               : 0.00
% 5.91/2.19  Total                : 1.46
% 5.91/2.19  Index Insertion      : 0.00
% 5.91/2.19  Index Deletion       : 0.00
% 5.91/2.19  Index Matching       : 0.00
% 5.91/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
