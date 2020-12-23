%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:05 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  97 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 347 expanded)
%              Number of equality atoms :   44 ( 151 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).

tff(f_64,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_26,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_187,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_3'(A_49,B_50),k1_relat_1(A_49))
      | B_50 = A_49
      | k1_relat_1(B_50) != k1_relat_1(A_49)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    k2_relat_1('#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_101,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(k1_funct_1(B_38,A_39),k2_relat_1(B_38))
      | ~ r2_hidden(A_39,k1_relat_1(B_38))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_107,plain,(
    ! [A_39] :
      ( r2_hidden(k1_funct_1('#skF_6',A_39),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_39,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_101])).

tff(c_117,plain,(
    ! [A_41] :
      ( r2_hidden(k1_funct_1('#skF_6',A_41),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_41,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_107])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_41] :
      ( k1_funct_1('#skF_6',A_41) = '#skF_4'
      | ~ r2_hidden(A_41,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_191,plain,(
    ! [B_50] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_50)) = '#skF_4'
      | B_50 = '#skF_6'
      | k1_relat_1(B_50) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_187,c_121])).

tff(c_201,plain,(
    ! [B_50] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_50)) = '#skF_4'
      | B_50 = '#skF_6'
      | k1_relat_1(B_50) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_191])).

tff(c_30,plain,(
    k2_relat_1('#skF_5') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_104,plain,(
    ! [A_39] :
      ( r2_hidden(k1_funct_1('#skF_5',A_39),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_39,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_101])).

tff(c_112,plain,(
    ! [A_40] :
      ( r2_hidden(k1_funct_1('#skF_5',A_40),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_40,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_104])).

tff(c_116,plain,(
    ! [A_40] :
      ( k1_funct_1('#skF_5',A_40) = '#skF_4'
      | ~ r2_hidden(A_40,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_195,plain,(
    ! [B_50] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_50)) = '#skF_4'
      | B_50 = '#skF_6'
      | k1_relat_1(B_50) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_187,c_116])).

tff(c_204,plain,(
    ! [B_50] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_50)) = '#skF_4'
      | B_50 = '#skF_6'
      | k1_relat_1(B_50) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_195])).

tff(c_318,plain,(
    ! [B_59,A_60] :
      ( k1_funct_1(B_59,'#skF_3'(A_60,B_59)) != k1_funct_1(A_60,'#skF_3'(A_60,B_59))
      | B_59 = A_60
      | k1_relat_1(B_59) != k1_relat_1(A_60)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_328,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_318])).

tff(c_334,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_36,c_34,c_40,c_38,c_32,c_328])).

tff(c_335,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_334])).

tff(c_338,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_335])).

tff(c_341,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_338])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:20:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.36  
% 2.16/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.36  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.36  
% 2.16/1.36  %Foreground sorts:
% 2.16/1.36  
% 2.16/1.36  
% 2.16/1.36  %Background operators:
% 2.16/1.36  
% 2.16/1.36  
% 2.16/1.36  %Foreground operators:
% 2.16/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.36  
% 2.16/1.38  tff(f_82, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 2.16/1.38  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 2.16/1.38  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.16/1.38  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.38  tff(c_26, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_32, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_187, plain, (![A_49, B_50]: (r2_hidden('#skF_3'(A_49, B_50), k1_relat_1(A_49)) | B_50=A_49 | k1_relat_1(B_50)!=k1_relat_1(A_49) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.38  tff(c_28, plain, (k2_relat_1('#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_101, plain, (![B_38, A_39]: (r2_hidden(k1_funct_1(B_38, A_39), k2_relat_1(B_38)) | ~r2_hidden(A_39, k1_relat_1(B_38)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.38  tff(c_107, plain, (![A_39]: (r2_hidden(k1_funct_1('#skF_6', A_39), k1_tarski('#skF_4')) | ~r2_hidden(A_39, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_101])).
% 2.16/1.38  tff(c_117, plain, (![A_41]: (r2_hidden(k1_funct_1('#skF_6', A_41), k1_tarski('#skF_4')) | ~r2_hidden(A_41, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_107])).
% 2.16/1.38  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.38  tff(c_121, plain, (![A_41]: (k1_funct_1('#skF_6', A_41)='#skF_4' | ~r2_hidden(A_41, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_117, c_2])).
% 2.16/1.38  tff(c_191, plain, (![B_50]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_50))='#skF_4' | B_50='#skF_6' | k1_relat_1(B_50)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_187, c_121])).
% 2.16/1.38  tff(c_201, plain, (![B_50]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_50))='#skF_4' | B_50='#skF_6' | k1_relat_1(B_50)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_191])).
% 2.16/1.38  tff(c_30, plain, (k2_relat_1('#skF_5')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.16/1.38  tff(c_104, plain, (![A_39]: (r2_hidden(k1_funct_1('#skF_5', A_39), k1_tarski('#skF_4')) | ~r2_hidden(A_39, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_101])).
% 2.16/1.38  tff(c_112, plain, (![A_40]: (r2_hidden(k1_funct_1('#skF_5', A_40), k1_tarski('#skF_4')) | ~r2_hidden(A_40, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_104])).
% 2.16/1.38  tff(c_116, plain, (![A_40]: (k1_funct_1('#skF_5', A_40)='#skF_4' | ~r2_hidden(A_40, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_112, c_2])).
% 2.16/1.38  tff(c_195, plain, (![B_50]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_50))='#skF_4' | B_50='#skF_6' | k1_relat_1(B_50)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_187, c_116])).
% 2.16/1.38  tff(c_204, plain, (![B_50]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_50))='#skF_4' | B_50='#skF_6' | k1_relat_1(B_50)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_195])).
% 2.16/1.38  tff(c_318, plain, (![B_59, A_60]: (k1_funct_1(B_59, '#skF_3'(A_60, B_59))!=k1_funct_1(A_60, '#skF_3'(A_60, B_59)) | B_59=A_60 | k1_relat_1(B_59)!=k1_relat_1(A_60) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.38  tff(c_328, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_204, c_318])).
% 2.16/1.38  tff(c_334, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_36, c_34, c_40, c_38, c_32, c_328])).
% 2.16/1.38  tff(c_335, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_334])).
% 2.16/1.38  tff(c_338, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_201, c_335])).
% 2.16/1.38  tff(c_341, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_338])).
% 2.16/1.38  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_341])).
% 2.16/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.38  
% 2.16/1.38  Inference rules
% 2.16/1.38  ----------------------
% 2.16/1.38  #Ref     : 1
% 2.16/1.38  #Sup     : 61
% 2.16/1.38  #Fact    : 0
% 2.16/1.38  #Define  : 0
% 2.16/1.38  #Split   : 0
% 2.16/1.38  #Chain   : 0
% 2.16/1.38  #Close   : 0
% 2.16/1.38  
% 2.16/1.38  Ordering : KBO
% 2.16/1.38  
% 2.16/1.38  Simplification rules
% 2.16/1.38  ----------------------
% 2.16/1.38  #Subsume      : 0
% 2.16/1.38  #Demod        : 63
% 2.16/1.38  #Tautology    : 43
% 2.16/1.38  #SimpNegUnit  : 2
% 2.16/1.38  #BackRed      : 0
% 2.16/1.38  
% 2.16/1.38  #Partial instantiations: 0
% 2.16/1.38  #Strategies tried      : 1
% 2.16/1.38  
% 2.16/1.38  Timing (in seconds)
% 2.16/1.38  ----------------------
% 2.16/1.38  Preprocessing        : 0.29
% 2.16/1.38  Parsing              : 0.15
% 2.16/1.38  CNF conversion       : 0.02
% 2.16/1.38  Main loop            : 0.23
% 2.16/1.38  Inferencing          : 0.09
% 2.16/1.38  Reduction            : 0.07
% 2.16/1.38  Demodulation         : 0.05
% 2.16/1.38  BG Simplification    : 0.02
% 2.16/1.38  Subsumption          : 0.04
% 2.16/1.38  Abstraction          : 0.02
% 2.16/1.38  MUC search           : 0.00
% 2.16/1.38  Cooper               : 0.00
% 2.16/1.38  Total                : 0.55
% 2.16/1.38  Index Insertion      : 0.00
% 2.16/1.38  Index Deletion       : 0.00
% 2.16/1.38  Index Matching       : 0.00
% 2.16/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
