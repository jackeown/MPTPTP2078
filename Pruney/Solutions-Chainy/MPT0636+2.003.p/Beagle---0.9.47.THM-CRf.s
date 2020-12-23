%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 108 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 264 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(c_30,plain,
    ( r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3'))))
    | r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,
    ( r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3'))))
    | r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_1] : v1_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_6] :
      ( k1_relat_1(k6_relat_1(A_6)) = A_6
      | ~ v1_funct_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_6] :
      ( k1_relat_1(k6_relat_1(A_6)) = A_6
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18])).

tff(c_40,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_136,plain,(
    ! [A_30,C_31,B_32] :
      ( r2_hidden(A_30,k1_relat_1(k5_relat_1(C_31,B_32)))
      | ~ r2_hidden(k1_funct_1(C_31,A_30),k1_relat_1(B_32))
      | ~ r2_hidden(A_30,k1_relat_1(C_31))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,(
    ! [A_30,C_31,A_6] :
      ( r2_hidden(A_30,k1_relat_1(k5_relat_1(C_31,k6_relat_1(A_6))))
      | ~ r2_hidden(k1_funct_1(C_31,A_30),A_6)
      | ~ r2_hidden(A_30,k1_relat_1(C_31))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31)
      | ~ v1_funct_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_136])).

tff(c_223,plain,(
    ! [A_43,C_44,A_45] :
      ( r2_hidden(A_43,k1_relat_1(k5_relat_1(C_44,k6_relat_1(A_45))))
      | ~ r2_hidden(k1_funct_1(C_44,A_43),A_45)
      | ~ r2_hidden(A_43,k1_relat_1(C_44))
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_145])).

tff(c_24,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_24])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_240,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_67])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_63,c_64,c_240])).

tff(c_253,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_253])).

tff(c_258,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_257,plain,(
    r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_297,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(k1_funct_1(C_51,A_52),k1_relat_1(B_53))
      | ~ r2_hidden(A_52,k1_relat_1(k5_relat_1(C_51,B_53)))
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_307,plain,(
    ! [C_51,A_52,A_6] :
      ( r2_hidden(k1_funct_1(C_51,A_52),A_6)
      | ~ r2_hidden(A_52,k1_relat_1(k5_relat_1(C_51,k6_relat_1(A_6))))
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_funct_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_297])).

tff(c_313,plain,(
    ! [C_54,A_55,A_56] :
      ( r2_hidden(k1_funct_1(C_54,A_55),A_56)
      | ~ r2_hidden(A_55,k1_relat_1(k5_relat_1(C_54,k6_relat_1(A_56))))
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_307])).

tff(c_324,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_313])).

tff(c_329,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_324])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_329])).

tff(c_333,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_332,plain,(
    r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_348,plain,(
    ! [A_58,C_59,B_60] :
      ( r2_hidden(A_58,k1_relat_1(C_59))
      | ~ r2_hidden(A_58,k1_relat_1(k5_relat_1(C_59,B_60)))
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_355,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k6_relat_1('#skF_3'))
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_332,c_348])).

tff(c_359,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_22,c_20,c_355])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.29/1.32  
% 2.29/1.32  %Foreground sorts:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Background operators:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Foreground operators:
% 2.29/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.32  
% 2.29/1.33  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_1)).
% 2.29/1.33  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.29/1.33  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.29/1.33  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 2.29/1.33  tff(c_30, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3')))) | r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.29/1.33  tff(c_64, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.29/1.33  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.29/1.33  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.29/1.33  tff(c_34, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3')))) | r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.29/1.33  tff(c_63, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.29/1.33  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.33  tff(c_4, plain, (![A_1]: (v1_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.33  tff(c_18, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6 | ~v1_funct_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.29/1.33  tff(c_36, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6 | ~v1_relat_1(k6_relat_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18])).
% 2.29/1.33  tff(c_40, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.29/1.33  tff(c_136, plain, (![A_30, C_31, B_32]: (r2_hidden(A_30, k1_relat_1(k5_relat_1(C_31, B_32))) | ~r2_hidden(k1_funct_1(C_31, A_30), k1_relat_1(B_32)) | ~r2_hidden(A_30, k1_relat_1(C_31)) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.33  tff(c_145, plain, (![A_30, C_31, A_6]: (r2_hidden(A_30, k1_relat_1(k5_relat_1(C_31, k6_relat_1(A_6)))) | ~r2_hidden(k1_funct_1(C_31, A_30), A_6) | ~r2_hidden(A_30, k1_relat_1(C_31)) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31) | ~v1_funct_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_136])).
% 2.29/1.33  tff(c_223, plain, (![A_43, C_44, A_45]: (r2_hidden(A_43, k1_relat_1(k5_relat_1(C_44, k6_relat_1(A_45)))) | ~r2_hidden(k1_funct_1(C_44, A_43), A_45) | ~r2_hidden(A_43, k1_relat_1(C_44)) | ~v1_funct_1(C_44) | ~v1_relat_1(C_44))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_145])).
% 2.29/1.33  tff(c_24, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.29/1.33  tff(c_66, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_24])).
% 2.29/1.33  tff(c_67, plain, (~r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3'))))), inference(splitLeft, [status(thm)], [c_66])).
% 2.29/1.33  tff(c_240, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_223, c_67])).
% 2.29/1.33  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_63, c_64, c_240])).
% 2.29/1.33  tff(c_253, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 2.29/1.33  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_253])).
% 2.29/1.33  tff(c_258, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.29/1.33  tff(c_257, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_30])).
% 2.29/1.33  tff(c_297, plain, (![C_51, A_52, B_53]: (r2_hidden(k1_funct_1(C_51, A_52), k1_relat_1(B_53)) | ~r2_hidden(A_52, k1_relat_1(k5_relat_1(C_51, B_53))) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.33  tff(c_307, plain, (![C_51, A_52, A_6]: (r2_hidden(k1_funct_1(C_51, A_52), A_6) | ~r2_hidden(A_52, k1_relat_1(k5_relat_1(C_51, k6_relat_1(A_6)))) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51) | ~v1_funct_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_297])).
% 2.29/1.33  tff(c_313, plain, (![C_54, A_55, A_56]: (r2_hidden(k1_funct_1(C_54, A_55), A_56) | ~r2_hidden(A_55, k1_relat_1(k5_relat_1(C_54, k6_relat_1(A_56)))) | ~v1_funct_1(C_54) | ~v1_relat_1(C_54))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_307])).
% 2.29/1.33  tff(c_324, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_257, c_313])).
% 2.29/1.33  tff(c_329, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_324])).
% 2.29/1.33  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_329])).
% 2.29/1.33  tff(c_333, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_34])).
% 2.29/1.33  tff(c_332, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_34])).
% 2.29/1.33  tff(c_348, plain, (![A_58, C_59, B_60]: (r2_hidden(A_58, k1_relat_1(C_59)) | ~r2_hidden(A_58, k1_relat_1(k5_relat_1(C_59, B_60))) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.33  tff(c_355, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k6_relat_1('#skF_3')) | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_332, c_348])).
% 2.29/1.33  tff(c_359, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_22, c_20, c_355])).
% 2.29/1.33  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_333, c_359])).
% 2.29/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  Inference rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Ref     : 0
% 2.29/1.33  #Sup     : 53
% 2.29/1.33  #Fact    : 0
% 2.29/1.33  #Define  : 0
% 2.29/1.33  #Split   : 3
% 2.29/1.33  #Chain   : 0
% 2.29/1.33  #Close   : 0
% 2.29/1.33  
% 2.29/1.33  Ordering : KBO
% 2.29/1.33  
% 2.29/1.33  Simplification rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Subsume      : 3
% 2.29/1.33  #Demod        : 99
% 2.29/1.33  #Tautology    : 25
% 2.29/1.33  #SimpNegUnit  : 2
% 2.29/1.33  #BackRed      : 0
% 2.29/1.33  
% 2.29/1.33  #Partial instantiations: 0
% 2.29/1.33  #Strategies tried      : 1
% 2.29/1.33  
% 2.29/1.33  Timing (in seconds)
% 2.29/1.33  ----------------------
% 2.29/1.33  Preprocessing        : 0.30
% 2.29/1.33  Parsing              : 0.16
% 2.29/1.33  CNF conversion       : 0.02
% 2.29/1.33  Main loop            : 0.24
% 2.29/1.33  Inferencing          : 0.09
% 2.29/1.33  Reduction            : 0.07
% 2.29/1.33  Demodulation         : 0.05
% 2.29/1.33  BG Simplification    : 0.02
% 2.29/1.33  Subsumption          : 0.05
% 2.29/1.33  Abstraction          : 0.01
% 2.29/1.33  MUC search           : 0.00
% 2.29/1.33  Cooper               : 0.00
% 2.29/1.33  Total                : 0.56
% 2.29/1.33  Index Insertion      : 0.00
% 2.29/1.33  Index Deletion       : 0.00
% 2.29/1.33  Index Matching       : 0.00
% 2.29/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
