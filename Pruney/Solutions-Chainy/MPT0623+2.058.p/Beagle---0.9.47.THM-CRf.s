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
% DateTime   : Thu Dec  3 10:03:13 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 179 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 484 expanded)
%              Number of equality atoms :   47 ( 203 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_40,plain,(
    ! [A_50,B_51] : v1_relat_1('#skF_7'(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_50,B_51] : v1_funct_1('#skF_7'(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_50,B_51] : k1_relat_1('#skF_7'(A_50,B_51)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_174,plain,(
    ! [A_98,C_99] :
      ( r2_hidden('#skF_6'(A_98,k2_relat_1(A_98),C_99),k1_relat_1(A_98))
      | ~ r2_hidden(C_99,k2_relat_1(A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_184,plain,(
    ! [A_50,B_51,C_99] :
      ( r2_hidden('#skF_6'('#skF_7'(A_50,B_51),k2_relat_1('#skF_7'(A_50,B_51)),C_99),A_50)
      | ~ r2_hidden(C_99,k2_relat_1('#skF_7'(A_50,B_51)))
      | ~ v1_funct_1('#skF_7'(A_50,B_51))
      | ~ v1_relat_1('#skF_7'(A_50,B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_174])).

tff(c_190,plain,(
    ! [A_50,B_51,C_99] :
      ( r2_hidden('#skF_6'('#skF_7'(A_50,B_51),k2_relat_1('#skF_7'(A_50,B_51)),C_99),A_50)
      | ~ r2_hidden(C_99,k2_relat_1('#skF_7'(A_50,B_51))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_184])).

tff(c_34,plain,(
    ! [A_50,B_51,D_56] :
      ( k1_funct_1('#skF_7'(A_50,B_51),D_56) = B_51
      | ~ r2_hidden(D_56,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_211,plain,(
    ! [A_105,C_106] :
      ( k1_funct_1(A_105,'#skF_6'(A_105,k2_relat_1(A_105),C_106)) = C_106
      | ~ r2_hidden(C_106,k2_relat_1(A_105))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [C_106,B_51,A_50] :
      ( C_106 = B_51
      | ~ r2_hidden(C_106,k2_relat_1('#skF_7'(A_50,B_51)))
      | ~ v1_funct_1('#skF_7'(A_50,B_51))
      | ~ v1_relat_1('#skF_7'(A_50,B_51))
      | ~ r2_hidden('#skF_6'('#skF_7'(A_50,B_51),k2_relat_1('#skF_7'(A_50,B_51)),C_106),A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_211])).

tff(c_2889,plain,(
    ! [C_300,B_301,A_302] :
      ( C_300 = B_301
      | ~ r2_hidden(C_300,k2_relat_1('#skF_7'(A_302,B_301)))
      | ~ r2_hidden('#skF_6'('#skF_7'(A_302,B_301),k2_relat_1('#skF_7'(A_302,B_301)),C_300),A_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_228])).

tff(c_2903,plain,(
    ! [C_303,B_304,A_305] :
      ( C_303 = B_304
      | ~ r2_hidden(C_303,k2_relat_1('#skF_7'(A_305,B_304))) ) ),
    inference(resolution,[status(thm)],[c_190,c_2889])).

tff(c_3659,plain,(
    ! [A_342,B_343,B_344] :
      ( '#skF_1'(k2_relat_1('#skF_7'(A_342,B_343)),B_344) = B_343
      | r1_tarski(k2_relat_1('#skF_7'(A_342,B_343)),B_344) ) ),
    inference(resolution,[status(thm)],[c_6,c_2903])).

tff(c_42,plain,(
    ! [C_58] :
      ( ~ r1_tarski(k2_relat_1(C_58),'#skF_8')
      | k1_relat_1(C_58) != '#skF_9'
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3764,plain,(
    ! [A_342,B_343] :
      ( k1_relat_1('#skF_7'(A_342,B_343)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_342,B_343))
      | ~ v1_relat_1('#skF_7'(A_342,B_343))
      | '#skF_1'(k2_relat_1('#skF_7'(A_342,B_343)),'#skF_8') = B_343 ) ),
    inference(resolution,[status(thm)],[c_3659,c_42])).

tff(c_3817,plain,(
    ! [A_345,B_346] :
      ( A_345 != '#skF_9'
      | '#skF_1'(k2_relat_1('#skF_7'(A_345,B_346)),'#skF_8') = B_346 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_3764])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4194,plain,(
    ! [B_360,A_361] :
      ( ~ r2_hidden(B_360,'#skF_8')
      | r1_tarski(k2_relat_1('#skF_7'(A_361,B_360)),'#skF_8')
      | A_361 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3817,c_4])).

tff(c_4228,plain,(
    ! [A_361,B_360] :
      ( k1_relat_1('#skF_7'(A_361,B_360)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_361,B_360))
      | ~ v1_relat_1('#skF_7'(A_361,B_360))
      | ~ r2_hidden(B_360,'#skF_8')
      | A_361 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_4194,c_42])).

tff(c_4252,plain,(
    ! [B_360,A_361] :
      ( ~ r2_hidden(B_360,'#skF_8')
      | A_361 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_4228])).

tff(c_4256,plain,(
    ! [A_361] : A_361 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4252])).

tff(c_4260,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4256])).

tff(c_4262,plain,(
    ! [B_362] : ~ r2_hidden(B_362,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_4252])).

tff(c_4306,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8,c_4262])).

tff(c_4319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4306])).

tff(c_4321,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4320,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4327,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4321,c_4320])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4322,plain,(
    ! [A_8] : r1_tarski('#skF_9',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4320,c_10])).

tff(c_4336,plain,(
    ! [A_8] : r1_tarski('#skF_8',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4327,c_4322])).

tff(c_14,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) = k1_xboole_0
      | k1_relat_1(A_9) != k1_xboole_0
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4370,plain,(
    ! [A_380] :
      ( k2_relat_1(A_380) = '#skF_8'
      | k1_relat_1(A_380) != '#skF_8'
      | ~ v1_relat_1(A_380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4321,c_4321,c_14])).

tff(c_4373,plain,(
    ! [A_50,B_51] :
      ( k2_relat_1('#skF_7'(A_50,B_51)) = '#skF_8'
      | k1_relat_1('#skF_7'(A_50,B_51)) != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_40,c_4370])).

tff(c_4377,plain,(
    ! [A_381,B_382] :
      ( k2_relat_1('#skF_7'(A_381,B_382)) = '#skF_8'
      | A_381 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4373])).

tff(c_4340,plain,(
    ! [C_58] :
      ( ~ r1_tarski(k2_relat_1(C_58),'#skF_8')
      | k1_relat_1(C_58) != '#skF_8'
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4327,c_42])).

tff(c_4386,plain,(
    ! [A_381,B_382] :
      ( ~ r1_tarski('#skF_8','#skF_8')
      | k1_relat_1('#skF_7'(A_381,B_382)) != '#skF_8'
      | ~ v1_funct_1('#skF_7'(A_381,B_382))
      | ~ v1_relat_1('#skF_7'(A_381,B_382))
      | A_381 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4377,c_4340])).

tff(c_4393,plain,(
    ! [A_381] : A_381 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_4336,c_4386])).

tff(c_4402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4393,c_4327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.88  
% 4.51/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.89  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 4.51/1.89  
% 4.51/1.89  %Foreground sorts:
% 4.51/1.89  
% 4.51/1.89  
% 4.51/1.89  %Background operators:
% 4.51/1.89  
% 4.51/1.89  
% 4.51/1.89  %Foreground operators:
% 4.51/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.89  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.51/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.89  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.51/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.51/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.51/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.51/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.51/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.51/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.89  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.51/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.51/1.89  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.51/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.51/1.89  
% 4.51/1.90  tff(f_75, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 4.51/1.90  tff(f_93, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 4.51/1.90  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.51/1.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.51/1.90  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.51/1.90  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.51/1.90  tff(f_48, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.51/1.90  tff(c_40, plain, (![A_50, B_51]: (v1_relat_1('#skF_7'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.90  tff(c_38, plain, (![A_50, B_51]: (v1_funct_1('#skF_7'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.90  tff(c_36, plain, (![A_50, B_51]: (k1_relat_1('#skF_7'(A_50, B_51))=A_50)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.90  tff(c_44, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.90  tff(c_46, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_44])).
% 4.51/1.90  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.51/1.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.90  tff(c_174, plain, (![A_98, C_99]: (r2_hidden('#skF_6'(A_98, k2_relat_1(A_98), C_99), k1_relat_1(A_98)) | ~r2_hidden(C_99, k2_relat_1(A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.51/1.90  tff(c_184, plain, (![A_50, B_51, C_99]: (r2_hidden('#skF_6'('#skF_7'(A_50, B_51), k2_relat_1('#skF_7'(A_50, B_51)), C_99), A_50) | ~r2_hidden(C_99, k2_relat_1('#skF_7'(A_50, B_51))) | ~v1_funct_1('#skF_7'(A_50, B_51)) | ~v1_relat_1('#skF_7'(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_174])).
% 4.51/1.90  tff(c_190, plain, (![A_50, B_51, C_99]: (r2_hidden('#skF_6'('#skF_7'(A_50, B_51), k2_relat_1('#skF_7'(A_50, B_51)), C_99), A_50) | ~r2_hidden(C_99, k2_relat_1('#skF_7'(A_50, B_51))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_184])).
% 4.51/1.90  tff(c_34, plain, (![A_50, B_51, D_56]: (k1_funct_1('#skF_7'(A_50, B_51), D_56)=B_51 | ~r2_hidden(D_56, A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.90  tff(c_211, plain, (![A_105, C_106]: (k1_funct_1(A_105, '#skF_6'(A_105, k2_relat_1(A_105), C_106))=C_106 | ~r2_hidden(C_106, k2_relat_1(A_105)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.51/1.90  tff(c_228, plain, (![C_106, B_51, A_50]: (C_106=B_51 | ~r2_hidden(C_106, k2_relat_1('#skF_7'(A_50, B_51))) | ~v1_funct_1('#skF_7'(A_50, B_51)) | ~v1_relat_1('#skF_7'(A_50, B_51)) | ~r2_hidden('#skF_6'('#skF_7'(A_50, B_51), k2_relat_1('#skF_7'(A_50, B_51)), C_106), A_50))), inference(superposition, [status(thm), theory('equality')], [c_34, c_211])).
% 4.51/1.90  tff(c_2889, plain, (![C_300, B_301, A_302]: (C_300=B_301 | ~r2_hidden(C_300, k2_relat_1('#skF_7'(A_302, B_301))) | ~r2_hidden('#skF_6'('#skF_7'(A_302, B_301), k2_relat_1('#skF_7'(A_302, B_301)), C_300), A_302))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_228])).
% 4.51/1.90  tff(c_2903, plain, (![C_303, B_304, A_305]: (C_303=B_304 | ~r2_hidden(C_303, k2_relat_1('#skF_7'(A_305, B_304))))), inference(resolution, [status(thm)], [c_190, c_2889])).
% 4.51/1.90  tff(c_3659, plain, (![A_342, B_343, B_344]: ('#skF_1'(k2_relat_1('#skF_7'(A_342, B_343)), B_344)=B_343 | r1_tarski(k2_relat_1('#skF_7'(A_342, B_343)), B_344))), inference(resolution, [status(thm)], [c_6, c_2903])).
% 4.51/1.90  tff(c_42, plain, (![C_58]: (~r1_tarski(k2_relat_1(C_58), '#skF_8') | k1_relat_1(C_58)!='#skF_9' | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.90  tff(c_3764, plain, (![A_342, B_343]: (k1_relat_1('#skF_7'(A_342, B_343))!='#skF_9' | ~v1_funct_1('#skF_7'(A_342, B_343)) | ~v1_relat_1('#skF_7'(A_342, B_343)) | '#skF_1'(k2_relat_1('#skF_7'(A_342, B_343)), '#skF_8')=B_343)), inference(resolution, [status(thm)], [c_3659, c_42])).
% 4.51/1.90  tff(c_3817, plain, (![A_345, B_346]: (A_345!='#skF_9' | '#skF_1'(k2_relat_1('#skF_7'(A_345, B_346)), '#skF_8')=B_346)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_3764])).
% 4.51/1.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.90  tff(c_4194, plain, (![B_360, A_361]: (~r2_hidden(B_360, '#skF_8') | r1_tarski(k2_relat_1('#skF_7'(A_361, B_360)), '#skF_8') | A_361!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3817, c_4])).
% 4.51/1.90  tff(c_4228, plain, (![A_361, B_360]: (k1_relat_1('#skF_7'(A_361, B_360))!='#skF_9' | ~v1_funct_1('#skF_7'(A_361, B_360)) | ~v1_relat_1('#skF_7'(A_361, B_360)) | ~r2_hidden(B_360, '#skF_8') | A_361!='#skF_9')), inference(resolution, [status(thm)], [c_4194, c_42])).
% 4.51/1.90  tff(c_4252, plain, (![B_360, A_361]: (~r2_hidden(B_360, '#skF_8') | A_361!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_4228])).
% 4.51/1.90  tff(c_4256, plain, (![A_361]: (A_361!='#skF_9')), inference(splitLeft, [status(thm)], [c_4252])).
% 4.51/1.90  tff(c_4260, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_4256])).
% 4.51/1.90  tff(c_4262, plain, (![B_362]: (~r2_hidden(B_362, '#skF_8'))), inference(splitRight, [status(thm)], [c_4252])).
% 4.51/1.90  tff(c_4306, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_8, c_4262])).
% 4.51/1.90  tff(c_4319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4306])).
% 4.51/1.90  tff(c_4321, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 4.51/1.90  tff(c_4320, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 4.51/1.90  tff(c_4327, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4321, c_4320])).
% 4.51/1.90  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.90  tff(c_4322, plain, (![A_8]: (r1_tarski('#skF_9', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4320, c_10])).
% 4.51/1.90  tff(c_4336, plain, (![A_8]: (r1_tarski('#skF_8', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4327, c_4322])).
% 4.51/1.90  tff(c_14, plain, (![A_9]: (k2_relat_1(A_9)=k1_xboole_0 | k1_relat_1(A_9)!=k1_xboole_0 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.51/1.90  tff(c_4370, plain, (![A_380]: (k2_relat_1(A_380)='#skF_8' | k1_relat_1(A_380)!='#skF_8' | ~v1_relat_1(A_380))), inference(demodulation, [status(thm), theory('equality')], [c_4321, c_4321, c_14])).
% 4.51/1.90  tff(c_4373, plain, (![A_50, B_51]: (k2_relat_1('#skF_7'(A_50, B_51))='#skF_8' | k1_relat_1('#skF_7'(A_50, B_51))!='#skF_8')), inference(resolution, [status(thm)], [c_40, c_4370])).
% 4.51/1.90  tff(c_4377, plain, (![A_381, B_382]: (k2_relat_1('#skF_7'(A_381, B_382))='#skF_8' | A_381!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4373])).
% 4.51/1.90  tff(c_4340, plain, (![C_58]: (~r1_tarski(k2_relat_1(C_58), '#skF_8') | k1_relat_1(C_58)!='#skF_8' | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(demodulation, [status(thm), theory('equality')], [c_4327, c_42])).
% 4.51/1.90  tff(c_4386, plain, (![A_381, B_382]: (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_7'(A_381, B_382))!='#skF_8' | ~v1_funct_1('#skF_7'(A_381, B_382)) | ~v1_relat_1('#skF_7'(A_381, B_382)) | A_381!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4377, c_4340])).
% 4.51/1.90  tff(c_4393, plain, (![A_381]: (A_381!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_4336, c_4386])).
% 4.51/1.90  tff(c_4402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4393, c_4327])).
% 4.51/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.90  
% 4.51/1.90  Inference rules
% 4.51/1.90  ----------------------
% 4.51/1.90  #Ref     : 3
% 4.51/1.90  #Sup     : 963
% 4.51/1.90  #Fact    : 0
% 4.51/1.90  #Define  : 0
% 4.51/1.90  #Split   : 5
% 4.51/1.90  #Chain   : 0
% 4.51/1.90  #Close   : 0
% 4.51/1.90  
% 4.51/1.90  Ordering : KBO
% 4.51/1.90  
% 4.51/1.90  Simplification rules
% 4.51/1.90  ----------------------
% 4.51/1.90  #Subsume      : 552
% 4.51/1.90  #Demod        : 473
% 4.51/1.90  #Tautology    : 130
% 4.51/1.90  #SimpNegUnit  : 63
% 4.51/1.90  #BackRed      : 11
% 4.51/1.90  
% 4.51/1.90  #Partial instantiations: 0
% 4.51/1.90  #Strategies tried      : 1
% 4.51/1.90  
% 4.51/1.90  Timing (in seconds)
% 4.51/1.90  ----------------------
% 4.51/1.90  Preprocessing        : 0.31
% 4.51/1.90  Parsing              : 0.16
% 4.51/1.90  CNF conversion       : 0.03
% 4.51/1.90  Main loop            : 0.77
% 4.51/1.90  Inferencing          : 0.27
% 4.51/1.90  Reduction            : 0.24
% 4.51/1.90  Demodulation         : 0.16
% 4.51/1.90  BG Simplification    : 0.03
% 4.51/1.90  Subsumption          : 0.18
% 4.51/1.90  Abstraction          : 0.04
% 4.51/1.90  MUC search           : 0.00
% 4.51/1.90  Cooper               : 0.00
% 4.51/1.90  Total                : 1.12
% 4.51/1.90  Index Insertion      : 0.00
% 4.51/1.90  Index Deletion       : 0.00
% 4.51/1.90  Index Matching       : 0.00
% 4.51/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
