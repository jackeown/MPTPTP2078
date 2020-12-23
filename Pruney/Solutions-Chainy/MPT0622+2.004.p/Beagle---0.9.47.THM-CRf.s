%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:05 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 101 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 351 expanded)
%              Number of equality atoms :   46 ( 155 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = k1_relat_1(C)
                & k2_relat_1(B) = k1_tarski(A)
                & k2_relat_1(C) = k1_tarski(A) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_53,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    k1_relat_1('#skF_10') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2216,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_7'(A_154,B_155),k1_relat_1(A_154))
      | B_155 = A_154
      | k1_relat_1(B_155) != k1_relat_1(A_154)
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    k2_relat_1('#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_117,plain,(
    ! [A_76,D_77] :
      ( r2_hidden(k1_funct_1(A_76,D_77),k2_relat_1(A_76))
      | ~ r2_hidden(D_77,k1_relat_1(A_76))
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [D_77] :
      ( r2_hidden(k1_funct_1('#skF_9',D_77),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_77,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_117])).

tff(c_128,plain,(
    ! [D_78] :
      ( r2_hidden(k1_funct_1('#skF_9',D_78),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_78,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_120])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [D_78] :
      ( k1_funct_1('#skF_9',D_78) = '#skF_8'
      | ~ r2_hidden(D_78,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_2224,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',B_155)) = '#skF_8'
      | B_155 = '#skF_9'
      | k1_relat_1(B_155) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2216,c_132])).

tff(c_2233,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',B_155)) = '#skF_8'
      | B_155 = '#skF_9'
      | k1_relat_1(B_155) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2224])).

tff(c_44,plain,(
    k2_relat_1('#skF_10') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_123,plain,(
    ! [D_77] :
      ( r2_hidden(k1_funct_1('#skF_10',D_77),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_77,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_117])).

tff(c_133,plain,(
    ! [D_79] :
      ( r2_hidden(k1_funct_1('#skF_10',D_79),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_79,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_123])).

tff(c_137,plain,(
    ! [D_79] :
      ( k1_funct_1('#skF_10',D_79) = '#skF_8'
      | ~ r2_hidden(D_79,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_133,c_2])).

tff(c_2220,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_10','#skF_7'('#skF_9',B_155)) = '#skF_8'
      | B_155 = '#skF_9'
      | k1_relat_1(B_155) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2216,c_137])).

tff(c_2230,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_10','#skF_7'('#skF_9',B_155)) = '#skF_8'
      | B_155 = '#skF_9'
      | k1_relat_1(B_155) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2220])).

tff(c_2722,plain,(
    ! [B_177,A_178] :
      ( k1_funct_1(B_177,'#skF_7'(A_178,B_177)) != k1_funct_1(A_178,'#skF_7'(A_178,B_177))
      | B_177 = A_178
      | k1_relat_1(B_177) != k1_relat_1(A_178)
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177)
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2732,plain,
    ( k1_funct_1('#skF_9','#skF_7'('#skF_9','#skF_10')) != '#skF_8'
    | '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2230,c_2722])).

tff(c_2738,plain,
    ( k1_funct_1('#skF_9','#skF_7'('#skF_9','#skF_10')) != '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_56,c_54,c_52,c_50,c_48,c_2732])).

tff(c_2739,plain,(
    k1_funct_1('#skF_9','#skF_7'('#skF_9','#skF_10')) != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2738])).

tff(c_2742,plain,
    ( '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_2739])).

tff(c_2745,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_2742])).

tff(c_2747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.85  
% 4.36/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.85  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 4.54/1.85  
% 4.54/1.85  %Foreground sorts:
% 4.54/1.85  
% 4.54/1.85  
% 4.54/1.85  %Background operators:
% 4.54/1.85  
% 4.54/1.85  
% 4.54/1.85  %Foreground operators:
% 4.54/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.54/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.54/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.54/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.54/1.85  tff('#skF_10', type, '#skF_10': $i).
% 4.54/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.54/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.85  tff('#skF_9', type, '#skF_9': $i).
% 4.54/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.54/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.54/1.85  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.54/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.54/1.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.54/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.54/1.85  
% 4.54/1.86  tff(f_89, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_1)).
% 4.54/1.86  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.54/1.86  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.54/1.86  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.54/1.86  tff(c_42, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_52, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_50, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_48, plain, (k1_relat_1('#skF_10')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_56, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_54, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_2216, plain, (![A_154, B_155]: (r2_hidden('#skF_7'(A_154, B_155), k1_relat_1(A_154)) | B_155=A_154 | k1_relat_1(B_155)!=k1_relat_1(A_154) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.54/1.86  tff(c_46, plain, (k2_relat_1('#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_117, plain, (![A_76, D_77]: (r2_hidden(k1_funct_1(A_76, D_77), k2_relat_1(A_76)) | ~r2_hidden(D_77, k1_relat_1(A_76)) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.86  tff(c_120, plain, (![D_77]: (r2_hidden(k1_funct_1('#skF_9', D_77), k1_tarski('#skF_8')) | ~r2_hidden(D_77, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_117])).
% 4.54/1.86  tff(c_128, plain, (![D_78]: (r2_hidden(k1_funct_1('#skF_9', D_78), k1_tarski('#skF_8')) | ~r2_hidden(D_78, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_120])).
% 4.54/1.86  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.86  tff(c_132, plain, (![D_78]: (k1_funct_1('#skF_9', D_78)='#skF_8' | ~r2_hidden(D_78, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_128, c_2])).
% 4.54/1.86  tff(c_2224, plain, (![B_155]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', B_155))='#skF_8' | B_155='#skF_9' | k1_relat_1(B_155)!=k1_relat_1('#skF_9') | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2216, c_132])).
% 4.54/1.86  tff(c_2233, plain, (![B_155]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', B_155))='#skF_8' | B_155='#skF_9' | k1_relat_1(B_155)!=k1_relat_1('#skF_9') | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2224])).
% 4.54/1.86  tff(c_44, plain, (k2_relat_1('#skF_10')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_123, plain, (![D_77]: (r2_hidden(k1_funct_1('#skF_10', D_77), k1_tarski('#skF_8')) | ~r2_hidden(D_77, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_117])).
% 4.54/1.86  tff(c_133, plain, (![D_79]: (r2_hidden(k1_funct_1('#skF_10', D_79), k1_tarski('#skF_8')) | ~r2_hidden(D_79, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_123])).
% 4.54/1.86  tff(c_137, plain, (![D_79]: (k1_funct_1('#skF_10', D_79)='#skF_8' | ~r2_hidden(D_79, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_133, c_2])).
% 4.54/1.86  tff(c_2220, plain, (![B_155]: (k1_funct_1('#skF_10', '#skF_7'('#skF_9', B_155))='#skF_8' | B_155='#skF_9' | k1_relat_1(B_155)!=k1_relat_1('#skF_9') | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2216, c_137])).
% 4.54/1.86  tff(c_2230, plain, (![B_155]: (k1_funct_1('#skF_10', '#skF_7'('#skF_9', B_155))='#skF_8' | B_155='#skF_9' | k1_relat_1(B_155)!=k1_relat_1('#skF_9') | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2220])).
% 4.54/1.86  tff(c_2722, plain, (![B_177, A_178]: (k1_funct_1(B_177, '#skF_7'(A_178, B_177))!=k1_funct_1(A_178, '#skF_7'(A_178, B_177)) | B_177=A_178 | k1_relat_1(B_177)!=k1_relat_1(A_178) | ~v1_funct_1(B_177) | ~v1_relat_1(B_177) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.54/1.86  tff(c_2732, plain, (k1_funct_1('#skF_9', '#skF_7'('#skF_9', '#skF_10'))!='#skF_8' | '#skF_10'='#skF_9' | k1_relat_1('#skF_10')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | '#skF_10'='#skF_9' | k1_relat_1('#skF_10')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2230, c_2722])).
% 4.54/1.86  tff(c_2738, plain, (k1_funct_1('#skF_9', '#skF_7'('#skF_9', '#skF_10'))!='#skF_8' | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_56, c_54, c_52, c_50, c_48, c_2732])).
% 4.54/1.86  tff(c_2739, plain, (k1_funct_1('#skF_9', '#skF_7'('#skF_9', '#skF_10'))!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_42, c_2738])).
% 4.54/1.86  tff(c_2742, plain, ('#skF_10'='#skF_9' | k1_relat_1('#skF_10')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2233, c_2739])).
% 4.54/1.86  tff(c_2745, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_2742])).
% 4.54/1.86  tff(c_2747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2745])).
% 4.54/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.86  
% 4.54/1.86  Inference rules
% 4.54/1.86  ----------------------
% 4.54/1.86  #Ref     : 2
% 4.54/1.86  #Sup     : 576
% 4.54/1.86  #Fact    : 0
% 4.54/1.86  #Define  : 0
% 4.54/1.86  #Split   : 5
% 4.54/1.86  #Chain   : 0
% 4.54/1.86  #Close   : 0
% 4.54/1.86  
% 4.54/1.86  Ordering : KBO
% 4.54/1.86  
% 4.54/1.86  Simplification rules
% 4.54/1.86  ----------------------
% 4.54/1.86  #Subsume      : 43
% 4.54/1.86  #Demod        : 813
% 4.54/1.86  #Tautology    : 304
% 4.54/1.86  #SimpNegUnit  : 17
% 4.54/1.86  #BackRed      : 19
% 4.54/1.86  
% 4.54/1.86  #Partial instantiations: 0
% 4.54/1.86  #Strategies tried      : 1
% 4.54/1.86  
% 4.54/1.86  Timing (in seconds)
% 4.54/1.86  ----------------------
% 4.54/1.86  Preprocessing        : 0.34
% 4.54/1.86  Parsing              : 0.17
% 4.54/1.86  CNF conversion       : 0.03
% 4.54/1.86  Main loop            : 0.72
% 4.54/1.86  Inferencing          : 0.25
% 4.54/1.86  Reduction            : 0.25
% 4.54/1.86  Demodulation         : 0.18
% 4.54/1.86  BG Simplification    : 0.04
% 4.54/1.86  Subsumption          : 0.14
% 4.54/1.86  Abstraction          : 0.04
% 4.54/1.86  MUC search           : 0.00
% 4.54/1.86  Cooper               : 0.00
% 4.54/1.86  Total                : 1.09
% 4.54/1.86  Index Insertion      : 0.00
% 4.54/1.86  Index Deletion       : 0.00
% 4.54/1.86  Index Matching       : 0.00
% 4.54/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
