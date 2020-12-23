%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:09 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 131 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 340 expanded)
%              Number of equality atoms :   63 ( 175 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_30,plain,(
    ! [A_12] : v1_relat_1('#skF_2'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_12] : v1_funct_1('#skF_2'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_12] : k1_relat_1('#skF_2'(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_18,B_22] :
      ( k1_relat_1('#skF_3'(A_18,B_22)) = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_18,B_22] :
      ( v1_funct_1('#skF_3'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_18,B_22] :
      ( v1_relat_1('#skF_3'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [A_56,B_57] :
      ( k2_relat_1('#skF_3'(A_56,B_57)) = k1_tarski(B_57)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [C_25] :
      ( ~ r1_tarski(k2_relat_1(C_25),'#skF_4')
      | k1_relat_1(C_25) != '#skF_5'
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_222,plain,(
    ! [B_65,A_66] :
      ( ~ r1_tarski(k1_tarski(B_65),'#skF_4')
      | k1_relat_1('#skF_3'(A_66,B_65)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_66,B_65))
      | ~ v1_relat_1('#skF_3'(A_66,B_65))
      | k1_xboole_0 = A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_40])).

tff(c_370,plain,(
    ! [A_87,A_88] :
      ( k1_relat_1('#skF_3'(A_87,A_88)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_87,A_88))
      | ~ v1_relat_1('#skF_3'(A_87,A_88))
      | k1_xboole_0 = A_87
      | ~ r2_hidden(A_88,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_222])).

tff(c_491,plain,(
    ! [A_109,B_110] :
      ( k1_relat_1('#skF_3'(A_109,B_110)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_109,B_110))
      | ~ r2_hidden(B_110,'#skF_4')
      | k1_xboole_0 = A_109 ) ),
    inference(resolution,[status(thm)],[c_38,c_370])).

tff(c_510,plain,(
    ! [A_115,B_116] :
      ( k1_relat_1('#skF_3'(A_115,B_116)) != '#skF_5'
      | ~ r2_hidden(B_116,'#skF_4')
      | k1_xboole_0 = A_115 ) ),
    inference(resolution,[status(thm)],[c_36,c_491])).

tff(c_513,plain,(
    ! [A_18,B_22] :
      ( A_18 != '#skF_5'
      | ~ r2_hidden(B_22,'#skF_4')
      | k1_xboole_0 = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_510])).

tff(c_515,plain,(
    ! [B_117] : ~ r2_hidden(B_117,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_526,plain,(
    ! [B_118] : r1_tarski('#skF_4',B_118) ),
    inference(resolution,[status(thm)],[c_6,c_515])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_128,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_128])).

tff(c_542,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_526,c_136])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_542])).

tff(c_556,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_93,plain,(
    ! [A_44] :
      ( k2_relat_1(A_44) = k1_xboole_0
      | k1_relat_1(A_44) != k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [A_12] :
      ( k2_relat_1('#skF_2'(A_12)) = k1_xboole_0
      | k1_relat_1('#skF_2'(A_12)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_93])).

tff(c_105,plain,(
    ! [A_46] :
      ( k2_relat_1('#skF_2'(A_46)) = k1_xboole_0
      | k1_xboole_0 != A_46 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_99])).

tff(c_114,plain,(
    ! [A_46] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4')
      | k1_relat_1('#skF_2'(A_46)) != '#skF_5'
      | ~ v1_funct_1('#skF_2'(A_46))
      | ~ v1_relat_1('#skF_2'(A_46))
      | k1_xboole_0 != A_46 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_40])).

tff(c_121,plain,(
    ! [A_46] :
      ( A_46 != '#skF_5'
      | k1_xboole_0 != A_46 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_14,c_114])).

tff(c_126,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_121])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_126])).

tff(c_582,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_22,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) = k1_xboole_0
      | k1_relat_1(A_11) != k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_655,plain,(
    ! [A_136] :
      ( k2_relat_1(A_136) = '#skF_4'
      | k1_relat_1(A_136) != '#skF_4'
      | ~ v1_relat_1(A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_582,c_22])).

tff(c_661,plain,(
    ! [A_12] :
      ( k2_relat_1('#skF_2'(A_12)) = '#skF_4'
      | k1_relat_1('#skF_2'(A_12)) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_30,c_655])).

tff(c_666,plain,(
    ! [A_137] :
      ( k2_relat_1('#skF_2'(A_137)) = '#skF_4'
      | A_137 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_661])).

tff(c_581,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_588,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_581])).

tff(c_614,plain,(
    ! [C_25] :
      ( ~ r1_tarski(k2_relat_1(C_25),'#skF_4')
      | k1_relat_1(C_25) != '#skF_4'
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_40])).

tff(c_675,plain,(
    ! [A_137] :
      ( ~ r1_tarski('#skF_4','#skF_4')
      | k1_relat_1('#skF_2'(A_137)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_137))
      | ~ v1_relat_1('#skF_2'(A_137))
      | A_137 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_614])).

tff(c_682,plain,(
    ! [A_137] : A_137 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_12,c_675])).

tff(c_694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:02:45 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.38  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 2.50/1.38  
% 2.50/1.38  %Foreground sorts:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Background operators:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Foreground operators:
% 2.50/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.50/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.38  
% 2.76/1.39  tff(f_62, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.76/1.39  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.39  tff(f_93, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 2.76/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.76/1.39  tff(f_75, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 2.76/1.39  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.76/1.39  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.39  tff(f_50, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.76/1.39  tff(c_30, plain, (![A_12]: (v1_relat_1('#skF_2'(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.39  tff(c_28, plain, (![A_12]: (v1_funct_1('#skF_2'(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.39  tff(c_26, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.39  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.39  tff(c_42, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.39  tff(c_57, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 2.76/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.39  tff(c_34, plain, (![A_18, B_22]: (k1_relat_1('#skF_3'(A_18, B_22))=A_18 | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.39  tff(c_36, plain, (![A_18, B_22]: (v1_funct_1('#skF_3'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.39  tff(c_38, plain, (![A_18, B_22]: (v1_relat_1('#skF_3'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.39  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.39  tff(c_175, plain, (![A_56, B_57]: (k2_relat_1('#skF_3'(A_56, B_57))=k1_tarski(B_57) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.39  tff(c_40, plain, (![C_25]: (~r1_tarski(k2_relat_1(C_25), '#skF_4') | k1_relat_1(C_25)!='#skF_5' | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.39  tff(c_222, plain, (![B_65, A_66]: (~r1_tarski(k1_tarski(B_65), '#skF_4') | k1_relat_1('#skF_3'(A_66, B_65))!='#skF_5' | ~v1_funct_1('#skF_3'(A_66, B_65)) | ~v1_relat_1('#skF_3'(A_66, B_65)) | k1_xboole_0=A_66)), inference(superposition, [status(thm), theory('equality')], [c_175, c_40])).
% 2.76/1.39  tff(c_370, plain, (![A_87, A_88]: (k1_relat_1('#skF_3'(A_87, A_88))!='#skF_5' | ~v1_funct_1('#skF_3'(A_87, A_88)) | ~v1_relat_1('#skF_3'(A_87, A_88)) | k1_xboole_0=A_87 | ~r2_hidden(A_88, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_222])).
% 2.76/1.39  tff(c_491, plain, (![A_109, B_110]: (k1_relat_1('#skF_3'(A_109, B_110))!='#skF_5' | ~v1_funct_1('#skF_3'(A_109, B_110)) | ~r2_hidden(B_110, '#skF_4') | k1_xboole_0=A_109)), inference(resolution, [status(thm)], [c_38, c_370])).
% 2.76/1.39  tff(c_510, plain, (![A_115, B_116]: (k1_relat_1('#skF_3'(A_115, B_116))!='#skF_5' | ~r2_hidden(B_116, '#skF_4') | k1_xboole_0=A_115)), inference(resolution, [status(thm)], [c_36, c_491])).
% 2.76/1.39  tff(c_513, plain, (![A_18, B_22]: (A_18!='#skF_5' | ~r2_hidden(B_22, '#skF_4') | k1_xboole_0=A_18 | k1_xboole_0=A_18)), inference(superposition, [status(thm), theory('equality')], [c_34, c_510])).
% 2.76/1.39  tff(c_515, plain, (![B_117]: (~r2_hidden(B_117, '#skF_4'))), inference(splitLeft, [status(thm)], [c_513])).
% 2.76/1.39  tff(c_526, plain, (![B_118]: (r1_tarski('#skF_4', B_118))), inference(resolution, [status(thm)], [c_6, c_515])).
% 2.76/1.39  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.39  tff(c_128, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.39  tff(c_136, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_128])).
% 2.76/1.39  tff(c_542, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_526, c_136])).
% 2.76/1.39  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_542])).
% 2.76/1.39  tff(c_556, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_513])).
% 2.76/1.39  tff(c_93, plain, (![A_44]: (k2_relat_1(A_44)=k1_xboole_0 | k1_relat_1(A_44)!=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.39  tff(c_99, plain, (![A_12]: (k2_relat_1('#skF_2'(A_12))=k1_xboole_0 | k1_relat_1('#skF_2'(A_12))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_93])).
% 2.76/1.39  tff(c_105, plain, (![A_46]: (k2_relat_1('#skF_2'(A_46))=k1_xboole_0 | k1_xboole_0!=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_99])).
% 2.76/1.39  tff(c_114, plain, (![A_46]: (~r1_tarski(k1_xboole_0, '#skF_4') | k1_relat_1('#skF_2'(A_46))!='#skF_5' | ~v1_funct_1('#skF_2'(A_46)) | ~v1_relat_1('#skF_2'(A_46)) | k1_xboole_0!=A_46)), inference(superposition, [status(thm), theory('equality')], [c_105, c_40])).
% 2.76/1.39  tff(c_121, plain, (![A_46]: (A_46!='#skF_5' | k1_xboole_0!=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_14, c_114])).
% 2.76/1.39  tff(c_126, plain, (k1_xboole_0!='#skF_5'), inference(reflexivity, [status(thm), theory('equality')], [c_121])).
% 2.76/1.39  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_126])).
% 2.76/1.39  tff(c_582, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.76/1.39  tff(c_22, plain, (![A_11]: (k2_relat_1(A_11)=k1_xboole_0 | k1_relat_1(A_11)!=k1_xboole_0 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.39  tff(c_655, plain, (![A_136]: (k2_relat_1(A_136)='#skF_4' | k1_relat_1(A_136)!='#skF_4' | ~v1_relat_1(A_136))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_582, c_22])).
% 2.76/1.39  tff(c_661, plain, (![A_12]: (k2_relat_1('#skF_2'(A_12))='#skF_4' | k1_relat_1('#skF_2'(A_12))!='#skF_4')), inference(resolution, [status(thm)], [c_30, c_655])).
% 2.76/1.39  tff(c_666, plain, (![A_137]: (k2_relat_1('#skF_2'(A_137))='#skF_4' | A_137!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_661])).
% 2.76/1.39  tff(c_581, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 2.76/1.39  tff(c_588, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_581])).
% 2.76/1.39  tff(c_614, plain, (![C_25]: (~r1_tarski(k2_relat_1(C_25), '#skF_4') | k1_relat_1(C_25)!='#skF_4' | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_40])).
% 2.76/1.39  tff(c_675, plain, (![A_137]: (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_2'(A_137))!='#skF_4' | ~v1_funct_1('#skF_2'(A_137)) | ~v1_relat_1('#skF_2'(A_137)) | A_137!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_666, c_614])).
% 2.76/1.39  tff(c_682, plain, (![A_137]: (A_137!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_12, c_675])).
% 2.76/1.39  tff(c_694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_682, c_588])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 1
% 2.76/1.39  #Sup     : 124
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 3
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.39  Ordering : KBO
% 2.76/1.39  
% 2.76/1.39  Simplification rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Subsume      : 37
% 2.76/1.39  #Demod        : 75
% 2.76/1.39  #Tautology    : 56
% 2.76/1.39  #SimpNegUnit  : 13
% 2.76/1.39  #BackRed      : 32
% 2.76/1.39  
% 2.76/1.39  #Partial instantiations: 0
% 2.76/1.39  #Strategies tried      : 1
% 2.76/1.39  
% 2.76/1.39  Timing (in seconds)
% 2.76/1.39  ----------------------
% 2.76/1.40  Preprocessing        : 0.30
% 2.76/1.40  Parsing              : 0.16
% 2.76/1.40  CNF conversion       : 0.02
% 2.76/1.40  Main loop            : 0.31
% 2.76/1.40  Inferencing          : 0.12
% 2.76/1.40  Reduction            : 0.08
% 2.76/1.40  Demodulation         : 0.06
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.06
% 2.76/1.40  Abstraction          : 0.02
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.64
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
