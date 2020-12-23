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
% DateTime   : Thu Dec  3 10:03:15 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 138 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 356 expanded)
%              Number of equality atoms :   62 ( 192 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_20,plain,(
    ! [A_7] : v1_relat_1('#skF_2'(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_7] : v1_funct_1('#skF_2'(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_7] : k1_relat_1('#skF_2'(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_13,B_17] :
      ( k1_relat_1('#skF_3'(A_13,B_17)) = A_13
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_13,B_17] :
      ( v1_funct_1('#skF_3'(A_13,B_17))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_13,B_17] :
      ( v1_relat_1('#skF_3'(A_13,B_17))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_44,B_45] :
      ( k2_relat_1('#skF_3'(A_44,B_45)) = k1_tarski(B_45)
      | k1_xboole_0 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [C_20] :
      ( ~ r1_tarski(k2_relat_1(C_20),'#skF_4')
      | k1_relat_1(C_20) != '#skF_5'
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_180,plain,(
    ! [B_52,A_53] :
      ( ~ r1_tarski(k1_tarski(B_52),'#skF_4')
      | k1_relat_1('#skF_3'(A_53,B_52)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_53,B_52))
      | ~ v1_relat_1('#skF_3'(A_53,B_52))
      | k1_xboole_0 = A_53 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_30])).

tff(c_191,plain,(
    ! [A_57,A_58] :
      ( k1_relat_1('#skF_3'(A_57,A_58)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_57,A_58))
      | ~ v1_relat_1('#skF_3'(A_57,A_58))
      | k1_xboole_0 = A_57
      | ~ r2_hidden(A_58,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_180])).

tff(c_197,plain,(
    ! [A_59,B_60] :
      ( k1_relat_1('#skF_3'(A_59,B_60)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_59,B_60))
      | ~ r2_hidden(B_60,'#skF_4')
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_28,c_191])).

tff(c_202,plain,(
    ! [A_61,B_62] :
      ( k1_relat_1('#skF_3'(A_61,B_62)) != '#skF_5'
      | ~ r2_hidden(B_62,'#skF_4')
      | k1_xboole_0 = A_61 ) ),
    inference(resolution,[status(thm)],[c_26,c_197])).

tff(c_205,plain,(
    ! [A_13,B_17] :
      ( A_13 != '#skF_5'
      | ~ r2_hidden(B_17,'#skF_4')
      | k1_xboole_0 = A_13
      | k1_xboole_0 = A_13 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_202])).

tff(c_207,plain,(
    ! [B_63] : ~ r2_hidden(B_63,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_211,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2,c_207])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_211])).

tff(c_217,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_41] :
      ( k2_relat_1(A_41) = k1_xboole_0
      | k1_relat_1(A_41) != k1_xboole_0
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [A_7] :
      ( k2_relat_1('#skF_2'(A_7)) = k1_xboole_0
      | k1_relat_1('#skF_2'(A_7)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_97,plain,(
    ! [A_42] :
      ( k2_relat_1('#skF_2'(A_42)) = k1_xboole_0
      | k1_xboole_0 != A_42 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_92])).

tff(c_106,plain,(
    ! [A_42] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4')
      | k1_relat_1('#skF_2'(A_42)) != '#skF_5'
      | ~ v1_funct_1('#skF_2'(A_42))
      | ~ v1_relat_1('#skF_2'(A_42))
      | k1_xboole_0 != A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_30])).

tff(c_113,plain,(
    ! [A_42] :
      ( A_42 != '#skF_5'
      | k1_xboole_0 != A_42 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_4,c_106])).

tff(c_118,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_113])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_118])).

tff(c_240,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_239,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_246,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_239])).

tff(c_241,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_4])).

tff(c_257,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_241])).

tff(c_12,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) = k1_xboole_0
      | k1_relat_1(A_6) != k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_318,plain,(
    ! [A_83] :
      ( k2_relat_1(A_83) = '#skF_4'
      | k1_relat_1(A_83) != '#skF_4'
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_240,c_12])).

tff(c_324,plain,(
    ! [A_7] :
      ( k2_relat_1('#skF_2'(A_7)) = '#skF_4'
      | k1_relat_1('#skF_2'(A_7)) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_20,c_318])).

tff(c_329,plain,(
    ! [A_84] :
      ( k2_relat_1('#skF_2'(A_84)) = '#skF_4'
      | A_84 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_324])).

tff(c_255,plain,(
    ! [C_20] :
      ( ~ r1_tarski(k2_relat_1(C_20),'#skF_4')
      | k1_relat_1(C_20) != '#skF_4'
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_30])).

tff(c_338,plain,(
    ! [A_84] :
      ( ~ r1_tarski('#skF_4','#skF_4')
      | k1_relat_1('#skF_2'(A_84)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_84))
      | ~ v1_relat_1('#skF_2'(A_84))
      | A_84 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_255])).

tff(c_345,plain,(
    ! [A_84] : A_84 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_257,c_338])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.07/1.27  
% 2.07/1.27  %Foreground sorts:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Background operators:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Foreground operators:
% 2.07/1.27  tff(np__1, type, np__1: $i).
% 2.07/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.27  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.07/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.27  
% 2.07/1.29  tff(f_57, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.07/1.29  tff(f_88, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.07/1.29  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.07/1.29  tff(f_70, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.07/1.29  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.07/1.29  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.07/1.29  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.07/1.29  tff(c_20, plain, (![A_7]: (v1_relat_1('#skF_2'(A_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.29  tff(c_18, plain, (![A_7]: (v1_funct_1('#skF_2'(A_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.29  tff(c_16, plain, (![A_7]: (k1_relat_1('#skF_2'(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.29  tff(c_32, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.29  tff(c_45, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 2.07/1.29  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.29  tff(c_24, plain, (![A_13, B_17]: (k1_relat_1('#skF_3'(A_13, B_17))=A_13 | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.07/1.29  tff(c_26, plain, (![A_13, B_17]: (v1_funct_1('#skF_3'(A_13, B_17)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.07/1.29  tff(c_28, plain, (![A_13, B_17]: (v1_relat_1('#skF_3'(A_13, B_17)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.07/1.29  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.29  tff(c_121, plain, (![A_44, B_45]: (k2_relat_1('#skF_3'(A_44, B_45))=k1_tarski(B_45) | k1_xboole_0=A_44)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.07/1.29  tff(c_30, plain, (![C_20]: (~r1_tarski(k2_relat_1(C_20), '#skF_4') | k1_relat_1(C_20)!='#skF_5' | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.29  tff(c_180, plain, (![B_52, A_53]: (~r1_tarski(k1_tarski(B_52), '#skF_4') | k1_relat_1('#skF_3'(A_53, B_52))!='#skF_5' | ~v1_funct_1('#skF_3'(A_53, B_52)) | ~v1_relat_1('#skF_3'(A_53, B_52)) | k1_xboole_0=A_53)), inference(superposition, [status(thm), theory('equality')], [c_121, c_30])).
% 2.07/1.29  tff(c_191, plain, (![A_57, A_58]: (k1_relat_1('#skF_3'(A_57, A_58))!='#skF_5' | ~v1_funct_1('#skF_3'(A_57, A_58)) | ~v1_relat_1('#skF_3'(A_57, A_58)) | k1_xboole_0=A_57 | ~r2_hidden(A_58, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_180])).
% 2.07/1.29  tff(c_197, plain, (![A_59, B_60]: (k1_relat_1('#skF_3'(A_59, B_60))!='#skF_5' | ~v1_funct_1('#skF_3'(A_59, B_60)) | ~r2_hidden(B_60, '#skF_4') | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_28, c_191])).
% 2.07/1.29  tff(c_202, plain, (![A_61, B_62]: (k1_relat_1('#skF_3'(A_61, B_62))!='#skF_5' | ~r2_hidden(B_62, '#skF_4') | k1_xboole_0=A_61)), inference(resolution, [status(thm)], [c_26, c_197])).
% 2.07/1.29  tff(c_205, plain, (![A_13, B_17]: (A_13!='#skF_5' | ~r2_hidden(B_17, '#skF_4') | k1_xboole_0=A_13 | k1_xboole_0=A_13)), inference(superposition, [status(thm), theory('equality')], [c_24, c_202])).
% 2.07/1.29  tff(c_207, plain, (![B_63]: (~r2_hidden(B_63, '#skF_4'))), inference(splitLeft, [status(thm)], [c_205])).
% 2.07/1.29  tff(c_211, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2, c_207])).
% 2.07/1.29  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_211])).
% 2.07/1.29  tff(c_217, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_205])).
% 2.07/1.29  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.29  tff(c_86, plain, (![A_41]: (k2_relat_1(A_41)=k1_xboole_0 | k1_relat_1(A_41)!=k1_xboole_0 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.29  tff(c_92, plain, (![A_7]: (k2_relat_1('#skF_2'(A_7))=k1_xboole_0 | k1_relat_1('#skF_2'(A_7))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_86])).
% 2.07/1.29  tff(c_97, plain, (![A_42]: (k2_relat_1('#skF_2'(A_42))=k1_xboole_0 | k1_xboole_0!=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_92])).
% 2.07/1.29  tff(c_106, plain, (![A_42]: (~r1_tarski(k1_xboole_0, '#skF_4') | k1_relat_1('#skF_2'(A_42))!='#skF_5' | ~v1_funct_1('#skF_2'(A_42)) | ~v1_relat_1('#skF_2'(A_42)) | k1_xboole_0!=A_42)), inference(superposition, [status(thm), theory('equality')], [c_97, c_30])).
% 2.07/1.29  tff(c_113, plain, (![A_42]: (A_42!='#skF_5' | k1_xboole_0!=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_4, c_106])).
% 2.07/1.29  tff(c_118, plain, (k1_xboole_0!='#skF_5'), inference(reflexivity, [status(thm), theory('equality')], [c_113])).
% 2.07/1.29  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_118])).
% 2.07/1.29  tff(c_240, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 2.07/1.29  tff(c_239, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_32])).
% 2.07/1.29  tff(c_246, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_239])).
% 2.07/1.29  tff(c_241, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_4])).
% 2.07/1.29  tff(c_257, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_241])).
% 2.07/1.29  tff(c_12, plain, (![A_6]: (k2_relat_1(A_6)=k1_xboole_0 | k1_relat_1(A_6)!=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.29  tff(c_318, plain, (![A_83]: (k2_relat_1(A_83)='#skF_4' | k1_relat_1(A_83)!='#skF_4' | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_240, c_12])).
% 2.07/1.29  tff(c_324, plain, (![A_7]: (k2_relat_1('#skF_2'(A_7))='#skF_4' | k1_relat_1('#skF_2'(A_7))!='#skF_4')), inference(resolution, [status(thm)], [c_20, c_318])).
% 2.07/1.29  tff(c_329, plain, (![A_84]: (k2_relat_1('#skF_2'(A_84))='#skF_4' | A_84!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_324])).
% 2.07/1.29  tff(c_255, plain, (![C_20]: (~r1_tarski(k2_relat_1(C_20), '#skF_4') | k1_relat_1(C_20)!='#skF_4' | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_30])).
% 2.07/1.29  tff(c_338, plain, (![A_84]: (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_2'(A_84))!='#skF_4' | ~v1_funct_1('#skF_2'(A_84)) | ~v1_relat_1('#skF_2'(A_84)) | A_84!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_329, c_255])).
% 2.07/1.29  tff(c_345, plain, (![A_84]: (A_84!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_257, c_338])).
% 2.07/1.29  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_246])).
% 2.07/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  Inference rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Ref     : 1
% 2.07/1.29  #Sup     : 57
% 2.07/1.29  #Fact    : 0
% 2.07/1.29  #Define  : 0
% 2.07/1.29  #Split   : 3
% 2.07/1.29  #Chain   : 0
% 2.07/1.29  #Close   : 0
% 2.07/1.29  
% 2.07/1.29  Ordering : KBO
% 2.07/1.29  
% 2.07/1.29  Simplification rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Subsume      : 12
% 2.07/1.29  #Demod        : 55
% 2.07/1.29  #Tautology    : 34
% 2.07/1.29  #SimpNegUnit  : 14
% 2.07/1.29  #BackRed      : 28
% 2.07/1.29  
% 2.07/1.29  #Partial instantiations: 0
% 2.07/1.29  #Strategies tried      : 1
% 2.07/1.29  
% 2.07/1.29  Timing (in seconds)
% 2.07/1.29  ----------------------
% 2.07/1.29  Preprocessing        : 0.29
% 2.07/1.29  Parsing              : 0.16
% 2.07/1.29  CNF conversion       : 0.02
% 2.07/1.29  Main loop            : 0.23
% 2.07/1.29  Inferencing          : 0.09
% 2.07/1.29  Reduction            : 0.06
% 2.07/1.29  Demodulation         : 0.04
% 2.07/1.29  BG Simplification    : 0.02
% 2.07/1.29  Subsumption          : 0.04
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.55
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
