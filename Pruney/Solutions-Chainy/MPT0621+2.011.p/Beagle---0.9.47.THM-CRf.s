%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:00 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 195 expanded)
%              Number of leaves         :   29 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 535 expanded)
%              Number of equality atoms :   68 ( 258 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_9 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_73,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_94,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_75,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc1_boole)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(c_10,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_2'(A_2),A_2)
      | v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_23] : v1_funct_1('#skF_7'(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_23] : k1_relat_1('#skF_7'(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_23] : v1_relat_1('#skF_7'(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_29] : k1_relat_1('#skF_8'(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_29] : v1_funct_1('#skF_8'(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_29] : v1_relat_1('#skF_8'(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    ! [C_46,B_47] :
      ( C_46 = B_47
      | k1_relat_1(C_46) != '#skF_9'
      | k1_relat_1(B_47) != '#skF_9'
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_54,plain,(
    ! [B_47,A_29] :
      ( B_47 = '#skF_8'(A_29)
      | k1_relat_1('#skF_8'(A_29)) != '#skF_9'
      | k1_relat_1(B_47) != '#skF_9'
      | ~ v1_funct_1('#skF_8'(A_29))
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_28,c_50])).

tff(c_60,plain,(
    ! [B_47,A_29] :
      ( B_47 = '#skF_8'(A_29)
      | k1_relat_1('#skF_8'(A_29)) != '#skF_9'
      | k1_relat_1(B_47) != '#skF_9'
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54])).

tff(c_110,plain,(
    ! [B_60,A_61] :
      ( B_60 = '#skF_8'(A_61)
      | A_61 != '#skF_9'
      | k1_relat_1(B_60) != '#skF_9'
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_60])).

tff(c_112,plain,(
    ! [A_61,A_23] :
      ( '#skF_8'(A_61) = '#skF_7'(A_23)
      | A_61 != '#skF_9'
      | k1_relat_1('#skF_7'(A_23)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_23)) ) ),
    inference(resolution,[status(thm)],[c_20,c_110])).

tff(c_122,plain,(
    ! [A_62,A_63] :
      ( '#skF_8'(A_62) = '#skF_7'(A_63)
      | A_62 != '#skF_9'
      | A_63 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_112])).

tff(c_22,plain,(
    ! [A_29,C_34] :
      ( k1_funct_1('#skF_8'(A_29),C_34) = np__1
      | ~ r2_hidden(C_34,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_365,plain,(
    ! [A_87,C_88,A_89] :
      ( k1_funct_1('#skF_7'(A_87),C_88) = np__1
      | ~ r2_hidden(C_88,A_89)
      | A_89 != '#skF_9'
      | A_87 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_22])).

tff(c_373,plain,(
    ! [A_90,A_91] :
      ( k1_funct_1('#skF_7'(A_90),'#skF_2'(A_91)) = np__1
      | A_91 != '#skF_9'
      | A_90 != '#skF_9'
      | v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_10,c_365])).

tff(c_39,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_39])).

tff(c_14,plain,(
    ! [A_23,C_28] :
      ( k1_funct_1('#skF_7'(A_23),C_28) = k1_xboole_0
      | ~ r2_hidden(C_28,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [A_23,C_28] :
      ( k1_funct_1('#skF_7'(A_23),C_28) = '#skF_1'
      | ~ r2_hidden(C_28,A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_14])).

tff(c_379,plain,(
    ! [A_91,A_90] :
      ( np__1 = '#skF_1'
      | ~ r2_hidden('#skF_2'(A_91),A_90)
      | A_91 != '#skF_9'
      | A_90 != '#skF_9'
      | v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_96])).

tff(c_466,plain,(
    np__1 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_30,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_502,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_30])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_502])).

tff(c_509,plain,(
    ! [A_101,A_102] :
      ( ~ r2_hidden('#skF_2'(A_101),A_102)
      | A_101 != '#skF_9'
      | A_102 != '#skF_9'
      | v1_relat_1(A_101) ) ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_513,plain,(
    ! [A_2] :
      ( A_2 != '#skF_9'
      | v1_relat_1(A_2) ) ),
    inference(resolution,[status(thm)],[c_10,c_509])).

tff(c_12,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | r2_hidden(k4_tarski('#skF_5'(A_20),'#skF_6'(A_20)),A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [A_20] :
      ( A_20 = '#skF_1'
      | r2_hidden(k4_tarski('#skF_5'(A_20),'#skF_6'(A_20)),A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_12])).

tff(c_507,plain,(
    np__1 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_530,plain,(
    ! [A_104,A_105] :
      ( k1_funct_1('#skF_7'(A_104),k4_tarski('#skF_5'(A_105),'#skF_6'(A_105))) = np__1
      | A_105 != '#skF_9'
      | A_104 != '#skF_9'
      | A_105 = '#skF_1'
      | ~ v1_relat_1(A_105) ) ),
    inference(resolution,[status(thm)],[c_106,c_365])).

tff(c_536,plain,(
    ! [A_105,A_104] :
      ( np__1 = '#skF_1'
      | ~ r2_hidden(k4_tarski('#skF_5'(A_105),'#skF_6'(A_105)),A_104)
      | A_105 != '#skF_9'
      | A_104 != '#skF_9'
      | A_105 = '#skF_1'
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_96])).

tff(c_590,plain,(
    ! [A_112,A_113] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_112),'#skF_6'(A_112)),A_113)
      | A_112 != '#skF_9'
      | A_113 != '#skF_9'
      | A_112 = '#skF_1'
      | ~ v1_relat_1(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_536])).

tff(c_596,plain,(
    ! [A_114] :
      ( A_114 != '#skF_9'
      | A_114 = '#skF_1'
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_106,c_590])).

tff(c_609,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_513,c_596])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_45,plain,(
    '#skF_1' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_32])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.37  
% 2.34/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.38  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > np__1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_9 > #skF_6 > #skF_4
% 2.34/1.38  
% 2.34/1.38  %Foreground sorts:
% 2.34/1.38  
% 2.34/1.38  
% 2.34/1.38  %Background operators:
% 2.34/1.38  
% 2.34/1.38  
% 2.34/1.38  %Foreground operators:
% 2.34/1.38  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.34/1.38  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.34/1.38  tff(np__1, type, np__1: $i).
% 2.34/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.34/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.38  tff('#skF_8', type, '#skF_8': $i > $i).
% 2.34/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.34/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.34/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.38  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.34/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.34/1.38  
% 2.88/1.39  tff(f_41, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.88/1.39  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.88/1.39  tff(f_61, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.88/1.39  tff(f_73, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.88/1.39  tff(f_94, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 2.88/1.39  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.88/1.39  tff(f_75, axiom, ~v1_xboole_0(np__1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', spc1_boole)).
% 2.88/1.39  tff(f_49, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 2.88/1.39  tff(c_10, plain, (![A_2]: (r2_hidden('#skF_2'(A_2), A_2) | v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.39  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.39  tff(c_18, plain, (![A_23]: (v1_funct_1('#skF_7'(A_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.39  tff(c_16, plain, (![A_23]: (k1_relat_1('#skF_7'(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.39  tff(c_20, plain, (![A_23]: (v1_relat_1('#skF_7'(A_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.39  tff(c_24, plain, (![A_29]: (k1_relat_1('#skF_8'(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.39  tff(c_26, plain, (![A_29]: (v1_funct_1('#skF_8'(A_29)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.39  tff(c_28, plain, (![A_29]: (v1_relat_1('#skF_8'(A_29)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.39  tff(c_50, plain, (![C_46, B_47]: (C_46=B_47 | k1_relat_1(C_46)!='#skF_9' | k1_relat_1(B_47)!='#skF_9' | ~v1_funct_1(C_46) | ~v1_relat_1(C_46) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.88/1.39  tff(c_54, plain, (![B_47, A_29]: (B_47='#skF_8'(A_29) | k1_relat_1('#skF_8'(A_29))!='#skF_9' | k1_relat_1(B_47)!='#skF_9' | ~v1_funct_1('#skF_8'(A_29)) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_28, c_50])).
% 2.88/1.39  tff(c_60, plain, (![B_47, A_29]: (B_47='#skF_8'(A_29) | k1_relat_1('#skF_8'(A_29))!='#skF_9' | k1_relat_1(B_47)!='#skF_9' | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54])).
% 2.88/1.39  tff(c_110, plain, (![B_60, A_61]: (B_60='#skF_8'(A_61) | A_61!='#skF_9' | k1_relat_1(B_60)!='#skF_9' | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_60])).
% 2.88/1.39  tff(c_112, plain, (![A_61, A_23]: ('#skF_8'(A_61)='#skF_7'(A_23) | A_61!='#skF_9' | k1_relat_1('#skF_7'(A_23))!='#skF_9' | ~v1_funct_1('#skF_7'(A_23)))), inference(resolution, [status(thm)], [c_20, c_110])).
% 2.88/1.39  tff(c_122, plain, (![A_62, A_63]: ('#skF_8'(A_62)='#skF_7'(A_63) | A_62!='#skF_9' | A_63!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_112])).
% 2.88/1.39  tff(c_22, plain, (![A_29, C_34]: (k1_funct_1('#skF_8'(A_29), C_34)=np__1 | ~r2_hidden(C_34, A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.39  tff(c_365, plain, (![A_87, C_88, A_89]: (k1_funct_1('#skF_7'(A_87), C_88)=np__1 | ~r2_hidden(C_88, A_89) | A_89!='#skF_9' | A_87!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_122, c_22])).
% 2.88/1.39  tff(c_373, plain, (![A_90, A_91]: (k1_funct_1('#skF_7'(A_90), '#skF_2'(A_91))=np__1 | A_91!='#skF_9' | A_90!='#skF_9' | v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_10, c_365])).
% 2.88/1.39  tff(c_39, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.39  tff(c_43, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_39])).
% 2.88/1.39  tff(c_14, plain, (![A_23, C_28]: (k1_funct_1('#skF_7'(A_23), C_28)=k1_xboole_0 | ~r2_hidden(C_28, A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.39  tff(c_96, plain, (![A_23, C_28]: (k1_funct_1('#skF_7'(A_23), C_28)='#skF_1' | ~r2_hidden(C_28, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_14])).
% 2.88/1.39  tff(c_379, plain, (![A_91, A_90]: (np__1='#skF_1' | ~r2_hidden('#skF_2'(A_91), A_90) | A_91!='#skF_9' | A_90!='#skF_9' | v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_373, c_96])).
% 2.88/1.39  tff(c_466, plain, (np__1='#skF_1'), inference(splitLeft, [status(thm)], [c_379])).
% 2.88/1.39  tff(c_30, plain, (~v1_xboole_0(np__1)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.88/1.39  tff(c_502, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_30])).
% 2.88/1.39  tff(c_505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_502])).
% 2.88/1.39  tff(c_509, plain, (![A_101, A_102]: (~r2_hidden('#skF_2'(A_101), A_102) | A_101!='#skF_9' | A_102!='#skF_9' | v1_relat_1(A_101))), inference(splitRight, [status(thm)], [c_379])).
% 2.88/1.39  tff(c_513, plain, (![A_2]: (A_2!='#skF_9' | v1_relat_1(A_2))), inference(resolution, [status(thm)], [c_10, c_509])).
% 2.88/1.39  tff(c_12, plain, (![A_20]: (k1_xboole_0=A_20 | r2_hidden(k4_tarski('#skF_5'(A_20), '#skF_6'(A_20)), A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.88/1.39  tff(c_106, plain, (![A_20]: (A_20='#skF_1' | r2_hidden(k4_tarski('#skF_5'(A_20), '#skF_6'(A_20)), A_20) | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_12])).
% 2.88/1.39  tff(c_507, plain, (np__1!='#skF_1'), inference(splitRight, [status(thm)], [c_379])).
% 2.88/1.39  tff(c_530, plain, (![A_104, A_105]: (k1_funct_1('#skF_7'(A_104), k4_tarski('#skF_5'(A_105), '#skF_6'(A_105)))=np__1 | A_105!='#skF_9' | A_104!='#skF_9' | A_105='#skF_1' | ~v1_relat_1(A_105))), inference(resolution, [status(thm)], [c_106, c_365])).
% 2.88/1.39  tff(c_536, plain, (![A_105, A_104]: (np__1='#skF_1' | ~r2_hidden(k4_tarski('#skF_5'(A_105), '#skF_6'(A_105)), A_104) | A_105!='#skF_9' | A_104!='#skF_9' | A_105='#skF_1' | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_530, c_96])).
% 2.88/1.39  tff(c_590, plain, (![A_112, A_113]: (~r2_hidden(k4_tarski('#skF_5'(A_112), '#skF_6'(A_112)), A_113) | A_112!='#skF_9' | A_113!='#skF_9' | A_112='#skF_1' | ~v1_relat_1(A_112))), inference(negUnitSimplification, [status(thm)], [c_507, c_536])).
% 2.88/1.39  tff(c_596, plain, (![A_114]: (A_114!='#skF_9' | A_114='#skF_1' | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_106, c_590])).
% 2.88/1.39  tff(c_609, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_513, c_596])).
% 2.88/1.39  tff(c_32, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.88/1.39  tff(c_45, plain, ('#skF_1'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_32])).
% 2.88/1.39  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_609, c_45])).
% 2.88/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.39  
% 2.88/1.39  Inference rules
% 2.88/1.39  ----------------------
% 2.88/1.39  #Ref     : 3
% 2.88/1.39  #Sup     : 135
% 2.88/1.39  #Fact    : 0
% 2.88/1.39  #Define  : 0
% 2.88/1.39  #Split   : 2
% 2.88/1.39  #Chain   : 0
% 2.88/1.39  #Close   : 0
% 2.88/1.39  
% 2.88/1.39  Ordering : KBO
% 2.88/1.39  
% 2.88/1.39  Simplification rules
% 2.88/1.39  ----------------------
% 2.88/1.39  #Subsume      : 70
% 2.88/1.39  #Demod        : 63
% 2.88/1.39  #Tautology    : 42
% 2.88/1.39  #SimpNegUnit  : 7
% 2.88/1.39  #BackRed      : 18
% 2.88/1.39  
% 2.88/1.39  #Partial instantiations: 0
% 2.88/1.39  #Strategies tried      : 1
% 2.88/1.39  
% 2.88/1.39  Timing (in seconds)
% 2.88/1.39  ----------------------
% 2.88/1.39  Preprocessing        : 0.29
% 2.88/1.39  Parsing              : 0.15
% 2.88/1.39  CNF conversion       : 0.02
% 2.88/1.39  Main loop            : 0.31
% 2.88/1.39  Inferencing          : 0.12
% 2.88/1.39  Reduction            : 0.10
% 2.88/1.39  Demodulation         : 0.07
% 2.88/1.39  BG Simplification    : 0.02
% 2.88/1.39  Subsumption          : 0.07
% 2.88/1.39  Abstraction          : 0.02
% 2.88/1.39  MUC search           : 0.00
% 2.88/1.39  Cooper               : 0.00
% 2.88/1.39  Total                : 0.63
% 2.88/1.39  Index Insertion      : 0.00
% 2.88/1.39  Index Deletion       : 0.00
% 2.88/1.39  Index Matching       : 0.00
% 2.88/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
