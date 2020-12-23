%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:37 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 176 expanded)
%              Number of leaves         :   22 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  103 ( 622 expanded)
%              Number of equality atoms :   35 ( 244 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = A )
             => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_40,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_30,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_5'(k1_relat_1(B_46),B_46),k1_relat_1(B_46))
      | k6_relat_1(k1_relat_1(B_46)) = B_46
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    k2_relat_1('#skF_6') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_61,plain,(
    ! [A_58,C_59] :
      ( k1_funct_1(A_58,'#skF_4'(A_58,k2_relat_1(A_58),C_59)) = C_59
      | ~ r2_hidden(C_59,k2_relat_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_59)) = C_59
      | ~ r2_hidden(C_59,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_61])).

tff(c_83,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_59)) = C_59
      | ~ r2_hidden(C_59,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_77])).

tff(c_6,plain,(
    ! [A_1,C_37] :
      ( r2_hidden('#skF_4'(A_1,k2_relat_1(A_1),C_37),k1_relat_1(A_1))
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    k5_relat_1('#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_135,plain,(
    ! [C_77,B_78,A_79] :
      ( k1_funct_1(k5_relat_1(C_77,B_78),A_79) = k1_funct_1(B_78,k1_funct_1(C_77,A_79))
      | ~ r2_hidden(A_79,k1_relat_1(k5_relat_1(C_77,B_78)))
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_79] :
      ( k1_funct_1(k5_relat_1('#skF_6','#skF_7'),A_79) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_79))
      | ~ r2_hidden(A_79,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_135])).

tff(c_171,plain,(
    ! [A_80] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_80)) = k1_funct_1('#skF_6',A_80)
      | ~ r2_hidden(A_80,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_40,c_32,c_162])).

tff(c_194,plain,(
    ! [C_37] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_37))) = k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_37))
      | ~ r2_hidden(C_37,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_517,plain,(
    ! [C_93] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_93))) = k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_93))
      | ~ r2_hidden(C_93,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_34,c_34,c_194])).

tff(c_542,plain,(
    ! [C_94] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_94)) = k1_funct_1('#skF_7',C_94)
      | ~ r2_hidden(C_94,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_94,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_517])).

tff(c_576,plain,(
    ! [C_95] :
      ( k1_funct_1('#skF_7',C_95) = C_95
      | ~ r2_hidden(C_95,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_95,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_95,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_83])).

tff(c_596,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_576])).

tff(c_613,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_596])).

tff(c_614,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_613])).

tff(c_620,plain,(
    ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_614])).

tff(c_623,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_620])).

tff(c_626,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_623])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_626])).

tff(c_629,plain,(
    k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_614])).

tff(c_22,plain,(
    ! [B_46] :
      ( k1_funct_1(B_46,'#skF_5'(k1_relat_1(B_46),B_46)) != '#skF_5'(k1_relat_1(B_46),B_46)
      | k6_relat_1(k1_relat_1(B_46)) = B_46
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_643,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_22])).

tff(c_655,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_643])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.37  
% 2.75/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.38  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.75/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.75/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.75/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.75/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.38  
% 2.75/1.39  tff(f_82, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 2.75/1.39  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.75/1.39  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.75/1.39  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 2.75/1.39  tff(c_30, plain, (k6_relat_1(k1_relat_1('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.39  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.39  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.39  tff(c_24, plain, (![B_46]: (r2_hidden('#skF_5'(k1_relat_1(B_46), B_46), k1_relat_1(B_46)) | k6_relat_1(k1_relat_1(B_46))=B_46 | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.75/1.39  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.39  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.39  tff(c_34, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.39  tff(c_61, plain, (![A_58, C_59]: (k1_funct_1(A_58, '#skF_4'(A_58, k2_relat_1(A_58), C_59))=C_59 | ~r2_hidden(C_59, k2_relat_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.39  tff(c_77, plain, (![C_59]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_59))=C_59 | ~r2_hidden(C_59, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_61])).
% 2.75/1.39  tff(c_83, plain, (![C_59]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_59))=C_59 | ~r2_hidden(C_59, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_77])).
% 2.75/1.39  tff(c_6, plain, (![A_1, C_37]: (r2_hidden('#skF_4'(A_1, k2_relat_1(A_1), C_37), k1_relat_1(A_1)) | ~r2_hidden(C_37, k2_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.39  tff(c_32, plain, (k5_relat_1('#skF_6', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.39  tff(c_135, plain, (![C_77, B_78, A_79]: (k1_funct_1(k5_relat_1(C_77, B_78), A_79)=k1_funct_1(B_78, k1_funct_1(C_77, A_79)) | ~r2_hidden(A_79, k1_relat_1(k5_relat_1(C_77, B_78))) | ~v1_funct_1(C_77) | ~v1_relat_1(C_77) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.39  tff(c_162, plain, (![A_79]: (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), A_79)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_79)) | ~r2_hidden(A_79, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_135])).
% 2.75/1.39  tff(c_171, plain, (![A_80]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_80))=k1_funct_1('#skF_6', A_80) | ~r2_hidden(A_80, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_42, c_40, c_32, c_162])).
% 2.75/1.39  tff(c_194, plain, (![C_37]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_37)))=k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_37)) | ~r2_hidden(C_37, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_171])).
% 2.75/1.39  tff(c_517, plain, (![C_93]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_93)))=k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_93)) | ~r2_hidden(C_93, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_34, c_34, c_194])).
% 2.75/1.39  tff(c_542, plain, (![C_94]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_94))=k1_funct_1('#skF_7', C_94) | ~r2_hidden(C_94, k1_relat_1('#skF_7')) | ~r2_hidden(C_94, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_83, c_517])).
% 2.75/1.39  tff(c_576, plain, (![C_95]: (k1_funct_1('#skF_7', C_95)=C_95 | ~r2_hidden(C_95, k1_relat_1('#skF_7')) | ~r2_hidden(C_95, k1_relat_1('#skF_7')) | ~r2_hidden(C_95, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_542, c_83])).
% 2.75/1.39  tff(c_596, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7')) | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_576])).
% 2.75/1.39  tff(c_613, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7')) | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_596])).
% 2.75/1.39  tff(c_614, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_30, c_613])).
% 2.75/1.39  tff(c_620, plain, (~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_614])).
% 2.75/1.39  tff(c_623, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_620])).
% 2.75/1.39  tff(c_626, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_623])).
% 2.75/1.39  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_626])).
% 2.75/1.39  tff(c_629, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_614])).
% 2.75/1.39  tff(c_22, plain, (![B_46]: (k1_funct_1(B_46, '#skF_5'(k1_relat_1(B_46), B_46))!='#skF_5'(k1_relat_1(B_46), B_46) | k6_relat_1(k1_relat_1(B_46))=B_46 | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.75/1.39  tff(c_643, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_629, c_22])).
% 2.75/1.39  tff(c_655, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_643])).
% 2.75/1.39  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_655])).
% 2.75/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  Inference rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Ref     : 0
% 2.75/1.39  #Sup     : 137
% 2.75/1.39  #Fact    : 0
% 2.75/1.39  #Define  : 0
% 2.75/1.39  #Split   : 4
% 2.75/1.39  #Chain   : 0
% 2.75/1.39  #Close   : 0
% 2.75/1.39  
% 2.75/1.39  Ordering : KBO
% 2.75/1.39  
% 2.75/1.39  Simplification rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Subsume      : 4
% 2.75/1.39  #Demod        : 155
% 2.75/1.39  #Tautology    : 40
% 2.75/1.39  #SimpNegUnit  : 7
% 2.75/1.39  #BackRed      : 1
% 2.75/1.39  
% 2.75/1.39  #Partial instantiations: 0
% 2.75/1.39  #Strategies tried      : 1
% 2.75/1.39  
% 2.75/1.39  Timing (in seconds)
% 2.75/1.39  ----------------------
% 2.75/1.39  Preprocessing        : 0.31
% 2.75/1.39  Parsing              : 0.16
% 2.75/1.39  CNF conversion       : 0.02
% 2.75/1.39  Main loop            : 0.33
% 2.75/1.39  Inferencing          : 0.12
% 2.75/1.39  Reduction            : 0.10
% 2.75/1.39  Demodulation         : 0.07
% 2.75/1.39  BG Simplification    : 0.03
% 2.75/1.39  Subsumption          : 0.05
% 2.75/1.39  Abstraction          : 0.02
% 2.75/1.39  MUC search           : 0.00
% 2.75/1.39  Cooper               : 0.00
% 2.75/1.39  Total                : 0.66
% 2.75/1.39  Index Insertion      : 0.00
% 2.75/1.39  Index Deletion       : 0.00
% 2.75/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
