%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:07 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 149 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 318 expanded)
%              Number of equality atoms :   51 ( 173 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_49,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_44,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_10,B_14] :
      ( k1_relat_1('#skF_2'(A_10,B_14)) = A_10
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [A_10,B_14] :
      ( v1_funct_1('#skF_2'(A_10,B_14))
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_10,B_14] :
      ( v1_relat_1('#skF_2'(A_10,B_14))
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_121,plain,(
    ! [A_36,B_37] :
      ( k2_relat_1('#skF_2'(A_36,B_37)) = k1_tarski(B_37)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [C_17] :
      ( ~ r1_tarski(k2_relat_1(C_17),'#skF_3')
      | k1_relat_1(C_17) != '#skF_4'
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_140,plain,(
    ! [B_39,A_40] :
      ( ~ r1_tarski(k1_tarski(B_39),'#skF_3')
      | k1_relat_1('#skF_2'(A_40,B_39)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_40,B_39))
      | ~ v1_relat_1('#skF_2'(A_40,B_39))
      | k1_xboole_0 = A_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_32])).

tff(c_145,plain,(
    ! [A_41,A_42] :
      ( k1_relat_1('#skF_2'(A_41,A_42)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_41,A_42))
      | ~ v1_relat_1('#skF_2'(A_41,A_42))
      | k1_xboole_0 = A_41
      | ~ r2_hidden(A_42,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_150,plain,(
    ! [A_43,B_44] :
      ( k1_relat_1('#skF_2'(A_43,B_44)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_43,B_44))
      | ~ r2_hidden(B_44,'#skF_3')
      | k1_xboole_0 = A_43 ) ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_155,plain,(
    ! [A_45,B_46] :
      ( k1_relat_1('#skF_2'(A_45,B_46)) != '#skF_4'
      | ~ r2_hidden(B_46,'#skF_3')
      | k1_xboole_0 = A_45 ) ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_158,plain,(
    ! [A_10,B_14] :
      ( A_10 != '#skF_4'
      | ~ r2_hidden(B_14,'#skF_3')
      | k1_xboole_0 = A_10
      | k1_xboole_0 = A_10 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_155])).

tff(c_160,plain,(
    ! [B_47] : ~ r2_hidden(B_47,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_164,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_164])).

tff(c_170,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_39,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_39])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_76,plain,(
    ! [A_22] :
      ( v1_funct_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_76])).

tff(c_59,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_43,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_43])).

tff(c_99,plain,(
    ! [C_33] :
      ( ~ r1_tarski(k2_relat_1(C_33),'#skF_3')
      | k1_relat_1(C_33) != '#skF_4'
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_102,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_3')
    | k1_relat_1(k1_xboole_0) != '#skF_4'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_80,c_68,c_6,c_102])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_107])).

tff(c_189,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_194,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_41])).

tff(c_191,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_189,c_68])).

tff(c_193,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_6])).

tff(c_195,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_189,c_20])).

tff(c_18,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_18])).

tff(c_190,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_201,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_190])).

tff(c_229,plain,(
    ! [C_49] :
      ( ~ r1_tarski(k2_relat_1(C_49),'#skF_4')
      | k1_relat_1(C_49) != '#skF_4'
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_32])).

tff(c_232,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_229])).

tff(c_237,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_191,c_193,c_232])).

tff(c_196,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_2])).

tff(c_242,plain,(
    ! [A_50] :
      ( v1_funct_1(A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_245,plain,(
    v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_242])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:19:17 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.22  
% 2.01/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.22  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.01/1.22  
% 2.01/1.22  %Foreground sorts:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Background operators:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Foreground operators:
% 2.01/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.01/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.01/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.01/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.22  
% 2.01/1.24  tff(f_84, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.01/1.24  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.01/1.24  tff(f_66, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.01/1.24  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.01/1.24  tff(f_49, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.01/1.24  tff(f_44, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.01/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.01/1.24  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.01/1.24  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.01/1.24  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.01/1.24  tff(c_34, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.01/1.24  tff(c_75, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 2.01/1.24  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.01/1.24  tff(c_26, plain, (![A_10, B_14]: (k1_relat_1('#skF_2'(A_10, B_14))=A_10 | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.24  tff(c_28, plain, (![A_10, B_14]: (v1_funct_1('#skF_2'(A_10, B_14)) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.24  tff(c_30, plain, (![A_10, B_14]: (v1_relat_1('#skF_2'(A_10, B_14)) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.24  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.01/1.24  tff(c_121, plain, (![A_36, B_37]: (k2_relat_1('#skF_2'(A_36, B_37))=k1_tarski(B_37) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.24  tff(c_32, plain, (![C_17]: (~r1_tarski(k2_relat_1(C_17), '#skF_3') | k1_relat_1(C_17)!='#skF_4' | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.01/1.24  tff(c_140, plain, (![B_39, A_40]: (~r1_tarski(k1_tarski(B_39), '#skF_3') | k1_relat_1('#skF_2'(A_40, B_39))!='#skF_4' | ~v1_funct_1('#skF_2'(A_40, B_39)) | ~v1_relat_1('#skF_2'(A_40, B_39)) | k1_xboole_0=A_40)), inference(superposition, [status(thm), theory('equality')], [c_121, c_32])).
% 2.01/1.24  tff(c_145, plain, (![A_41, A_42]: (k1_relat_1('#skF_2'(A_41, A_42))!='#skF_4' | ~v1_funct_1('#skF_2'(A_41, A_42)) | ~v1_relat_1('#skF_2'(A_41, A_42)) | k1_xboole_0=A_41 | ~r2_hidden(A_42, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_140])).
% 2.01/1.24  tff(c_150, plain, (![A_43, B_44]: (k1_relat_1('#skF_2'(A_43, B_44))!='#skF_4' | ~v1_funct_1('#skF_2'(A_43, B_44)) | ~r2_hidden(B_44, '#skF_3') | k1_xboole_0=A_43)), inference(resolution, [status(thm)], [c_30, c_145])).
% 2.01/1.24  tff(c_155, plain, (![A_45, B_46]: (k1_relat_1('#skF_2'(A_45, B_46))!='#skF_4' | ~r2_hidden(B_46, '#skF_3') | k1_xboole_0=A_45)), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.01/1.24  tff(c_158, plain, (![A_10, B_14]: (A_10!='#skF_4' | ~r2_hidden(B_14, '#skF_3') | k1_xboole_0=A_10 | k1_xboole_0=A_10)), inference(superposition, [status(thm), theory('equality')], [c_26, c_155])).
% 2.01/1.24  tff(c_160, plain, (![B_47]: (~r2_hidden(B_47, '#skF_3'))), inference(splitLeft, [status(thm)], [c_158])).
% 2.01/1.24  tff(c_164, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_160])).
% 2.01/1.24  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_164])).
% 2.01/1.24  tff(c_170, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_158])).
% 2.01/1.24  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.24  tff(c_39, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.24  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_39])).
% 2.01/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.01/1.24  tff(c_76, plain, (![A_22]: (v1_funct_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.24  tff(c_80, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_76])).
% 2.01/1.24  tff(c_59, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.24  tff(c_68, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_59])).
% 2.01/1.24  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.01/1.24  tff(c_43, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.24  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_43])).
% 2.01/1.24  tff(c_99, plain, (![C_33]: (~r1_tarski(k2_relat_1(C_33), '#skF_3') | k1_relat_1(C_33)!='#skF_4' | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.01/1.24  tff(c_102, plain, (~r1_tarski(k1_xboole_0, '#skF_3') | k1_relat_1(k1_xboole_0)!='#skF_4' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_99])).
% 2.01/1.24  tff(c_107, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_80, c_68, c_6, c_102])).
% 2.01/1.24  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_107])).
% 2.01/1.24  tff(c_189, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 2.01/1.24  tff(c_194, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_41])).
% 2.01/1.24  tff(c_191, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_189, c_68])).
% 2.01/1.24  tff(c_193, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_6])).
% 2.01/1.24  tff(c_195, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_189, c_20])).
% 2.01/1.24  tff(c_18, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.24  tff(c_212, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_195, c_18])).
% 2.01/1.24  tff(c_190, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.01/1.24  tff(c_201, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_190])).
% 2.01/1.24  tff(c_229, plain, (![C_49]: (~r1_tarski(k2_relat_1(C_49), '#skF_4') | k1_relat_1(C_49)!='#skF_4' | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_32])).
% 2.01/1.24  tff(c_232, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_212, c_229])).
% 2.01/1.24  tff(c_237, plain, (~v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_191, c_193, c_232])).
% 2.01/1.24  tff(c_196, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_2])).
% 2.01/1.24  tff(c_242, plain, (![A_50]: (v1_funct_1(A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.24  tff(c_245, plain, (v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_196, c_242])).
% 2.01/1.24  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_245])).
% 2.01/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.24  
% 2.01/1.24  Inference rules
% 2.01/1.24  ----------------------
% 2.01/1.24  #Ref     : 0
% 2.01/1.24  #Sup     : 46
% 2.01/1.24  #Fact    : 0
% 2.01/1.24  #Define  : 0
% 2.01/1.24  #Split   : 2
% 2.01/1.24  #Chain   : 0
% 2.01/1.24  #Close   : 0
% 2.01/1.24  
% 2.01/1.24  Ordering : KBO
% 2.01/1.24  
% 2.01/1.24  Simplification rules
% 2.01/1.24  ----------------------
% 2.01/1.24  #Subsume      : 4
% 2.01/1.24  #Demod        : 46
% 2.01/1.24  #Tautology    : 30
% 2.01/1.24  #SimpNegUnit  : 2
% 2.01/1.24  #BackRed      : 22
% 2.01/1.24  
% 2.01/1.24  #Partial instantiations: 0
% 2.01/1.24  #Strategies tried      : 1
% 2.01/1.24  
% 2.01/1.24  Timing (in seconds)
% 2.01/1.24  ----------------------
% 2.01/1.24  Preprocessing        : 0.29
% 2.01/1.24  Parsing              : 0.16
% 2.01/1.24  CNF conversion       : 0.02
% 2.01/1.24  Main loop            : 0.18
% 2.01/1.24  Inferencing          : 0.07
% 2.01/1.24  Reduction            : 0.05
% 2.01/1.24  Demodulation         : 0.04
% 2.01/1.24  BG Simplification    : 0.01
% 2.01/1.24  Subsumption          : 0.03
% 2.01/1.24  Abstraction          : 0.01
% 2.01/1.24  MUC search           : 0.00
% 2.01/1.24  Cooper               : 0.00
% 2.01/1.24  Total                : 0.51
% 2.01/1.24  Index Insertion      : 0.00
% 2.01/1.24  Index Deletion       : 0.00
% 2.01/1.24  Index Matching       : 0.00
% 2.01/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
