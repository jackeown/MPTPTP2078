%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:40 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 222 expanded)
%              Number of equality atoms :   37 (  89 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
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
    k6_relat_1('#skF_3') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_102,plain,(
    ! [A_25] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_25)),A_25) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_102])).

tff(c_125,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117])).

tff(c_14,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_5] : v1_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_3] : k2_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_227,plain,(
    ! [C_38,B_39,A_40] :
      ( C_38 = B_39
      | k5_relat_1(C_38,A_40) != k5_relat_1(B_39,A_40)
      | k1_relat_1(C_38) != k1_relat_1(B_39)
      | ~ r1_tarski(k2_relat_1(C_38),k1_relat_1(A_40))
      | ~ r1_tarski(k2_relat_1(B_39),k1_relat_1(A_40))
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_249,plain,(
    ! [B_39] :
      ( B_39 = '#skF_5'
      | k5_relat_1(B_39,'#skF_4') != '#skF_4'
      | k1_relat_1(B_39) != k1_relat_1('#skF_5')
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_39),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_227])).

tff(c_293,plain,(
    ! [B_44] :
      ( B_44 = '#skF_5'
      | k5_relat_1(B_44,'#skF_4') != '#skF_4'
      | k1_relat_1(B_44) != '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_44),'#skF_3')
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_52,c_50,c_48,c_44,c_48,c_46,c_249])).

tff(c_304,plain,(
    ! [A_3] :
      ( k6_relat_1(A_3) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_3),'#skF_4') != '#skF_4'
      | k1_relat_1(k6_relat_1(A_3)) != '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3')
      | ~ v1_funct_1(k6_relat_1(A_3))
      | ~ v1_relat_1(k6_relat_1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_293])).

tff(c_317,plain,(
    ! [A_45] :
      ( k6_relat_1(A_45) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_45),'#skF_4') != '#skF_4'
      | A_45 != '#skF_3'
      | ~ r1_tarski(A_45,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_8,c_304])).

tff(c_320,plain,
    ( k6_relat_1('#skF_3') = '#skF_5'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_317])).

tff(c_327,plain,(
    k6_relat_1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_320])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.04/1.25  
% 2.04/1.25  %Foreground sorts:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Background operators:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Foreground operators:
% 2.04/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.04/1.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.04/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.25  
% 2.04/1.27  tff(f_91, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 2.04/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.27  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 2.04/1.27  tff(f_43, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.04/1.27  tff(f_35, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.04/1.27  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((r1_tarski(k2_relat_1(B), k1_relat_1(A)) & r1_tarski(k2_relat_1(C), k1_relat_1(A))) & (k1_relat_1(B) = k1_relat_1(C))) & (k5_relat_1(B, A) = k5_relat_1(C, A))) => (B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_1)).
% 2.04/1.27  tff(c_38, plain, (k6_relat_1('#skF_3')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.27  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_48, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_102, plain, (![A_25]: (k5_relat_1(k6_relat_1(k1_relat_1(A_25)), A_25)=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.27  tff(c_117, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_102])).
% 2.04/1.27  tff(c_125, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117])).
% 2.04/1.27  tff(c_14, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.27  tff(c_16, plain, (![A_5]: (v1_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.27  tff(c_8, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.27  tff(c_10, plain, (![A_3]: (k2_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.27  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_42, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_44, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_46, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_40, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.27  tff(c_227, plain, (![C_38, B_39, A_40]: (C_38=B_39 | k5_relat_1(C_38, A_40)!=k5_relat_1(B_39, A_40) | k1_relat_1(C_38)!=k1_relat_1(B_39) | ~r1_tarski(k2_relat_1(C_38), k1_relat_1(A_40)) | ~r1_tarski(k2_relat_1(B_39), k1_relat_1(A_40)) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.04/1.27  tff(c_249, plain, (![B_39]: (B_39='#skF_5' | k5_relat_1(B_39, '#skF_4')!='#skF_4' | k1_relat_1(B_39)!=k1_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_39), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_227])).
% 2.04/1.27  tff(c_293, plain, (![B_44]: (B_44='#skF_5' | k5_relat_1(B_44, '#skF_4')!='#skF_4' | k1_relat_1(B_44)!='#skF_3' | ~r1_tarski(k2_relat_1(B_44), '#skF_3') | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_52, c_50, c_48, c_44, c_48, c_46, c_249])).
% 2.04/1.27  tff(c_304, plain, (![A_3]: (k6_relat_1(A_3)='#skF_5' | k5_relat_1(k6_relat_1(A_3), '#skF_4')!='#skF_4' | k1_relat_1(k6_relat_1(A_3))!='#skF_3' | ~r1_tarski(A_3, '#skF_3') | ~v1_funct_1(k6_relat_1(A_3)) | ~v1_relat_1(k6_relat_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_293])).
% 2.04/1.27  tff(c_317, plain, (![A_45]: (k6_relat_1(A_45)='#skF_5' | k5_relat_1(k6_relat_1(A_45), '#skF_4')!='#skF_4' | A_45!='#skF_3' | ~r1_tarski(A_45, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_8, c_304])).
% 2.04/1.27  tff(c_320, plain, (k6_relat_1('#skF_3')='#skF_5' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125, c_317])).
% 2.04/1.27  tff(c_327, plain, (k6_relat_1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_320])).
% 2.04/1.27  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_327])).
% 2.04/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.27  
% 2.04/1.27  Inference rules
% 2.04/1.27  ----------------------
% 2.04/1.27  #Ref     : 1
% 2.04/1.27  #Sup     : 62
% 2.04/1.27  #Fact    : 0
% 2.04/1.27  #Define  : 0
% 2.04/1.27  #Split   : 2
% 2.04/1.27  #Chain   : 0
% 2.04/1.27  #Close   : 0
% 2.04/1.27  
% 2.04/1.27  Ordering : KBO
% 2.04/1.27  
% 2.04/1.27  Simplification rules
% 2.04/1.27  ----------------------
% 2.04/1.27  #Subsume      : 1
% 2.04/1.27  #Demod        : 125
% 2.04/1.27  #Tautology    : 33
% 2.04/1.27  #SimpNegUnit  : 1
% 2.04/1.27  #BackRed      : 0
% 2.04/1.27  
% 2.04/1.27  #Partial instantiations: 0
% 2.04/1.27  #Strategies tried      : 1
% 2.04/1.27  
% 2.04/1.27  Timing (in seconds)
% 2.04/1.27  ----------------------
% 2.04/1.27  Preprocessing        : 0.29
% 2.04/1.27  Parsing              : 0.14
% 2.04/1.27  CNF conversion       : 0.02
% 2.04/1.27  Main loop            : 0.26
% 2.04/1.27  Inferencing          : 0.09
% 2.04/1.27  Reduction            : 0.08
% 2.04/1.27  Demodulation         : 0.06
% 2.04/1.27  BG Simplification    : 0.02
% 2.04/1.27  Subsumption          : 0.06
% 2.04/1.27  Abstraction          : 0.02
% 2.04/1.27  MUC search           : 0.00
% 2.04/1.27  Cooper               : 0.00
% 2.04/1.27  Total                : 0.58
% 2.04/1.27  Index Insertion      : 0.00
% 2.04/1.27  Index Deletion       : 0.00
% 2.04/1.27  Index Matching       : 0.00
% 2.04/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
