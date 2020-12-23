%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 229 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( r1_tarski(k2_relat_1(B),k1_relat_1(A))
                    & r1_tarski(k2_relat_1(C),k1_relat_1(A))
                    & k1_relat_1(B) = k1_relat_1(C)
                    & k5_relat_1(B,A) = k5_relat_1(C,A) )
                 => B = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).

tff(c_38,plain,(
    k6_relat_1('#skF_4') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_131,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_29] : r1_tarski(A_29,A_29) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_27)),A_27) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,
    ( k5_relat_1(k6_relat_1('#skF_4'),'#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_90])).

tff(c_113,plain,(
    k5_relat_1(k6_relat_1('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_105])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_8] : v1_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_44,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    k5_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_297,plain,(
    ! [C_64,B_65,A_66] :
      ( C_64 = B_65
      | k5_relat_1(C_64,A_66) != k5_relat_1(B_65,A_66)
      | k1_relat_1(C_64) != k1_relat_1(B_65)
      | ~ r1_tarski(k2_relat_1(C_64),k1_relat_1(A_66))
      | ~ r1_tarski(k2_relat_1(B_65),k1_relat_1(A_66))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_319,plain,(
    ! [B_65] :
      ( B_65 = '#skF_6'
      | k5_relat_1(B_65,'#skF_5') != '#skF_5'
      | k1_relat_1(B_65) != k1_relat_1('#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_5'))
      | ~ r1_tarski(k2_relat_1(B_65),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_297])).

tff(c_342,plain,(
    ! [B_67] :
      ( B_67 = '#skF_6'
      | k5_relat_1(B_67,'#skF_5') != '#skF_5'
      | k1_relat_1(B_67) != '#skF_4'
      | ~ r1_tarski(k2_relat_1(B_67),'#skF_4')
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_52,c_50,c_48,c_44,c_48,c_46,c_319])).

tff(c_353,plain,(
    ! [A_6] :
      ( k6_relat_1(A_6) = '#skF_6'
      | k5_relat_1(k6_relat_1(A_6),'#skF_5') != '#skF_5'
      | k1_relat_1(k6_relat_1(A_6)) != '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4')
      | ~ v1_funct_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_342])).

tff(c_366,plain,(
    ! [A_68] :
      ( k6_relat_1(A_68) = '#skF_6'
      | k5_relat_1(k6_relat_1(A_68),'#skF_5') != '#skF_5'
      | A_68 != '#skF_4'
      | ~ r1_tarski(A_68,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_8,c_353])).

tff(c_369,plain,
    ( k6_relat_1('#skF_4') = '#skF_6'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_366])).

tff(c_376,plain,(
    k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_369])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.33  
% 2.54/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.33  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.54/1.33  
% 2.54/1.33  %Foreground sorts:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Background operators:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Foreground operators:
% 2.54/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.54/1.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.54/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.54/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.33  
% 2.54/1.35  tff(f_92, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 2.54/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.54/1.35  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 2.54/1.35  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.54/1.35  tff(f_36, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.54/1.35  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((r1_tarski(k2_relat_1(B), k1_relat_1(A)) & r1_tarski(k2_relat_1(C), k1_relat_1(A))) & (k1_relat_1(B) = k1_relat_1(C))) & (k5_relat_1(B, A) = k5_relat_1(C, A))) => (B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_1)).
% 2.54/1.35  tff(c_38, plain, (k6_relat_1('#skF_4')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_131, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), A_29) | r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.35  tff(c_136, plain, (![A_29]: (r1_tarski(A_29, A_29))), inference(resolution, [status(thm)], [c_131, c_4])).
% 2.54/1.35  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_48, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_90, plain, (![A_27]: (k5_relat_1(k6_relat_1(k1_relat_1(A_27)), A_27)=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.54/1.35  tff(c_105, plain, (k5_relat_1(k6_relat_1('#skF_4'), '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_90])).
% 2.54/1.35  tff(c_113, plain, (k5_relat_1(k6_relat_1('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_105])).
% 2.54/1.35  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.54/1.35  tff(c_16, plain, (![A_8]: (v1_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.54/1.35  tff(c_8, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.54/1.35  tff(c_10, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.54/1.35  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_42, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_44, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_46, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_40, plain, (k5_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.54/1.35  tff(c_297, plain, (![C_64, B_65, A_66]: (C_64=B_65 | k5_relat_1(C_64, A_66)!=k5_relat_1(B_65, A_66) | k1_relat_1(C_64)!=k1_relat_1(B_65) | ~r1_tarski(k2_relat_1(C_64), k1_relat_1(A_66)) | ~r1_tarski(k2_relat_1(B_65), k1_relat_1(A_66)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.35  tff(c_319, plain, (![B_65]: (B_65='#skF_6' | k5_relat_1(B_65, '#skF_5')!='#skF_5' | k1_relat_1(B_65)!=k1_relat_1('#skF_6') | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_5')) | ~r1_tarski(k2_relat_1(B_65), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(B_65) | ~v1_relat_1(B_65) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_297])).
% 2.54/1.35  tff(c_342, plain, (![B_67]: (B_67='#skF_6' | k5_relat_1(B_67, '#skF_5')!='#skF_5' | k1_relat_1(B_67)!='#skF_4' | ~r1_tarski(k2_relat_1(B_67), '#skF_4') | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_52, c_50, c_48, c_44, c_48, c_46, c_319])).
% 2.54/1.35  tff(c_353, plain, (![A_6]: (k6_relat_1(A_6)='#skF_6' | k5_relat_1(k6_relat_1(A_6), '#skF_5')!='#skF_5' | k1_relat_1(k6_relat_1(A_6))!='#skF_4' | ~r1_tarski(A_6, '#skF_4') | ~v1_funct_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_342])).
% 2.54/1.35  tff(c_366, plain, (![A_68]: (k6_relat_1(A_68)='#skF_6' | k5_relat_1(k6_relat_1(A_68), '#skF_5')!='#skF_5' | A_68!='#skF_4' | ~r1_tarski(A_68, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_8, c_353])).
% 2.54/1.35  tff(c_369, plain, (k6_relat_1('#skF_4')='#skF_6' | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_113, c_366])).
% 2.54/1.35  tff(c_376, plain, (k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_369])).
% 2.54/1.35  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_376])).
% 2.54/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  Inference rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Ref     : 1
% 2.54/1.35  #Sup     : 73
% 2.54/1.35  #Fact    : 0
% 2.54/1.35  #Define  : 0
% 2.54/1.35  #Split   : 2
% 2.54/1.35  #Chain   : 0
% 2.54/1.35  #Close   : 0
% 2.54/1.35  
% 2.54/1.35  Ordering : KBO
% 2.54/1.35  
% 2.54/1.35  Simplification rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Subsume      : 2
% 2.54/1.35  #Demod        : 114
% 2.54/1.35  #Tautology    : 32
% 2.54/1.35  #SimpNegUnit  : 1
% 2.54/1.35  #BackRed      : 0
% 2.54/1.35  
% 2.54/1.35  #Partial instantiations: 0
% 2.54/1.35  #Strategies tried      : 1
% 2.54/1.35  
% 2.54/1.35  Timing (in seconds)
% 2.54/1.35  ----------------------
% 2.86/1.35  Preprocessing        : 0.31
% 2.86/1.35  Parsing              : 0.16
% 2.86/1.35  CNF conversion       : 0.02
% 2.86/1.35  Main loop            : 0.29
% 2.86/1.35  Inferencing          : 0.11
% 2.86/1.35  Reduction            : 0.09
% 2.86/1.35  Demodulation         : 0.06
% 2.86/1.35  BG Simplification    : 0.02
% 2.86/1.35  Subsumption          : 0.06
% 2.86/1.35  Abstraction          : 0.02
% 2.86/1.35  MUC search           : 0.00
% 2.86/1.35  Cooper               : 0.00
% 2.86/1.35  Total                : 0.63
% 2.86/1.35  Index Insertion      : 0.00
% 2.86/1.35  Index Deletion       : 0.00
% 2.86/1.35  Index Matching       : 0.00
% 2.86/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
