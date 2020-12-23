%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:18 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 180 expanded)
%              Number of leaves         :   23 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 510 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k8_relat_1(A_19,B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k8_relat_1(A_19,B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,
    ( r2_hidden('#skF_8',k1_relat_1(k8_relat_1('#skF_9','#skF_10')))
    | r2_hidden('#skF_8',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_79,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,
    ( r2_hidden('#skF_8',k1_relat_1(k8_relat_1('#skF_9','#skF_10')))
    | r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_318,plain,(
    ! [D_98,A_99,C_100] :
      ( r2_hidden(D_98,k1_relat_1(k8_relat_1(A_99,C_100)))
      | ~ r2_hidden(k1_funct_1(C_100,D_98),A_99)
      | ~ r2_hidden(D_98,k1_relat_1(C_100))
      | ~ v1_funct_1(C_100)
      | ~ v1_relat_1(C_100)
      | ~ v1_funct_1(k8_relat_1(A_99,C_100))
      | ~ v1_relat_1(k8_relat_1(A_99,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_8',k1_relat_1(k8_relat_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1(k8_relat_1('#skF_9','#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_80,c_66])).

tff(c_340,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_318,c_83])).

tff(c_353,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_79,c_80,c_340])).

tff(c_355,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_358,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_22,c_355])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_358])).

tff(c_363,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_367,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_20,c_363])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_367])).

tff(c_373,plain,(
    ~ r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_372,plain,(
    r2_hidden('#skF_8',k1_relat_1(k8_relat_1('#skF_9','#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_429,plain,(
    ! [C_124,D_125,A_126] :
      ( r2_hidden(k1_funct_1(C_124,D_125),A_126)
      | ~ r2_hidden(D_125,k1_relat_1(k8_relat_1(A_126,C_124)))
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_funct_1(k8_relat_1(A_126,C_124))
      | ~ v1_relat_1(k8_relat_1(A_126,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_436,plain,
    ( r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_372,c_429])).

tff(c_440,plain,
    ( r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9')
    | ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_436])).

tff(c_441,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_440])).

tff(c_442,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_445,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_22,c_442])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_445])).

tff(c_450,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_454,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_20,c_450])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_454])).

tff(c_460,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_459,plain,(
    r2_hidden('#skF_8',k1_relat_1(k8_relat_1('#skF_9','#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_505,plain,(
    ! [D_147,C_148,A_149] :
      ( r2_hidden(D_147,k1_relat_1(C_148))
      | ~ r2_hidden(D_147,k1_relat_1(k8_relat_1(A_149,C_148)))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148)
      | ~ v1_funct_1(k8_relat_1(A_149,C_148))
      | ~ v1_relat_1(k8_relat_1(A_149,C_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_512,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_459,c_505])).

tff(c_516,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_512])).

tff(c_517,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_516])).

tff(c_518,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_521,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_22,c_518])).

tff(c_525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_521])).

tff(c_526,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_530,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_20,c_526])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:53:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.45  
% 3.04/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.46  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3
% 3.04/1.46  
% 3.04/1.46  %Foreground sorts:
% 3.04/1.46  
% 3.04/1.46  
% 3.04/1.46  %Background operators:
% 3.04/1.46  
% 3.04/1.46  
% 3.04/1.46  %Foreground operators:
% 3.04/1.46  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.04/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.04/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.46  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.04/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.04/1.46  tff('#skF_10', type, '#skF_10': $i).
% 3.04/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.04/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.04/1.46  tff('#skF_9', type, '#skF_9': $i).
% 3.04/1.46  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.04/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.04/1.46  tff('#skF_8', type, '#skF_8': $i).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.04/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.46  
% 3.17/1.47  tff(f_91, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 3.17/1.47  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 3.17/1.47  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_1)).
% 3.17/1.47  tff(c_64, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.47  tff(c_62, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.47  tff(c_20, plain, (![A_19, B_20]: (v1_funct_1(k8_relat_1(A_19, B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.47  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k8_relat_1(A_19, B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.47  tff(c_76, plain, (r2_hidden('#skF_8', k1_relat_1(k8_relat_1('#skF_9', '#skF_10'))) | r2_hidden('#skF_8', k1_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.47  tff(c_79, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_76])).
% 3.17/1.47  tff(c_72, plain, (r2_hidden('#skF_8', k1_relat_1(k8_relat_1('#skF_9', '#skF_10'))) | r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.47  tff(c_80, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_72])).
% 3.17/1.47  tff(c_318, plain, (![D_98, A_99, C_100]: (r2_hidden(D_98, k1_relat_1(k8_relat_1(A_99, C_100))) | ~r2_hidden(k1_funct_1(C_100, D_98), A_99) | ~r2_hidden(D_98, k1_relat_1(C_100)) | ~v1_funct_1(C_100) | ~v1_relat_1(C_100) | ~v1_funct_1(k8_relat_1(A_99, C_100)) | ~v1_relat_1(k8_relat_1(A_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.47  tff(c_66, plain, (~r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9') | ~r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden('#skF_8', k1_relat_1(k8_relat_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.47  tff(c_83, plain, (~r2_hidden('#skF_8', k1_relat_1(k8_relat_1('#skF_9', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_80, c_66])).
% 3.17/1.47  tff(c_340, plain, (~r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9') | ~r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_318, c_83])).
% 3.17/1.47  tff(c_353, plain, (~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_79, c_80, c_340])).
% 3.17/1.47  tff(c_355, plain, (~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_353])).
% 3.17/1.47  tff(c_358, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_22, c_355])).
% 3.17/1.47  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_358])).
% 3.17/1.47  tff(c_363, plain, (~v1_funct_1(k8_relat_1('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_353])).
% 3.17/1.47  tff(c_367, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_20, c_363])).
% 3.17/1.47  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_367])).
% 3.17/1.47  tff(c_373, plain, (~r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_72])).
% 3.17/1.47  tff(c_372, plain, (r2_hidden('#skF_8', k1_relat_1(k8_relat_1('#skF_9', '#skF_10')))), inference(splitRight, [status(thm)], [c_72])).
% 3.17/1.47  tff(c_429, plain, (![C_124, D_125, A_126]: (r2_hidden(k1_funct_1(C_124, D_125), A_126) | ~r2_hidden(D_125, k1_relat_1(k8_relat_1(A_126, C_124))) | ~v1_funct_1(C_124) | ~v1_relat_1(C_124) | ~v1_funct_1(k8_relat_1(A_126, C_124)) | ~v1_relat_1(k8_relat_1(A_126, C_124)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.47  tff(c_436, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_372, c_429])).
% 3.17/1.47  tff(c_440, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9') | ~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_436])).
% 3.17/1.47  tff(c_441, plain, (~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_373, c_440])).
% 3.17/1.47  tff(c_442, plain, (~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_441])).
% 3.17/1.47  tff(c_445, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_22, c_442])).
% 3.17/1.47  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_445])).
% 3.17/1.47  tff(c_450, plain, (~v1_funct_1(k8_relat_1('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_441])).
% 3.17/1.47  tff(c_454, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_20, c_450])).
% 3.17/1.47  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_454])).
% 3.17/1.47  tff(c_460, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_76])).
% 3.17/1.47  tff(c_459, plain, (r2_hidden('#skF_8', k1_relat_1(k8_relat_1('#skF_9', '#skF_10')))), inference(splitRight, [status(thm)], [c_76])).
% 3.17/1.47  tff(c_505, plain, (![D_147, C_148, A_149]: (r2_hidden(D_147, k1_relat_1(C_148)) | ~r2_hidden(D_147, k1_relat_1(k8_relat_1(A_149, C_148))) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148) | ~v1_funct_1(k8_relat_1(A_149, C_148)) | ~v1_relat_1(k8_relat_1(A_149, C_148)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.47  tff(c_512, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_459, c_505])).
% 3.17/1.47  tff(c_516, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_512])).
% 3.17/1.47  tff(c_517, plain, (~v1_funct_1(k8_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_460, c_516])).
% 3.17/1.47  tff(c_518, plain, (~v1_relat_1(k8_relat_1('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_517])).
% 3.17/1.47  tff(c_521, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_22, c_518])).
% 3.17/1.47  tff(c_525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_521])).
% 3.17/1.47  tff(c_526, plain, (~v1_funct_1(k8_relat_1('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_517])).
% 3.17/1.47  tff(c_530, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_20, c_526])).
% 3.17/1.47  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_530])).
% 3.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  Inference rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Ref     : 0
% 3.17/1.47  #Sup     : 86
% 3.17/1.47  #Fact    : 0
% 3.17/1.47  #Define  : 0
% 3.17/1.47  #Split   : 5
% 3.17/1.47  #Chain   : 0
% 3.17/1.47  #Close   : 0
% 3.17/1.47  
% 3.17/1.47  Ordering : KBO
% 3.17/1.47  
% 3.17/1.47  Simplification rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Subsume      : 4
% 3.17/1.47  #Demod        : 29
% 3.17/1.47  #Tautology    : 21
% 3.17/1.47  #SimpNegUnit  : 2
% 3.17/1.47  #BackRed      : 0
% 3.17/1.47  
% 3.17/1.47  #Partial instantiations: 0
% 3.17/1.47  #Strategies tried      : 1
% 3.17/1.47  
% 3.17/1.47  Timing (in seconds)
% 3.17/1.47  ----------------------
% 3.17/1.47  Preprocessing        : 0.34
% 3.17/1.47  Parsing              : 0.17
% 3.17/1.47  CNF conversion       : 0.03
% 3.17/1.47  Main loop            : 0.32
% 3.17/1.47  Inferencing          : 0.11
% 3.17/1.47  Reduction            : 0.08
% 3.17/1.47  Demodulation         : 0.06
% 3.17/1.47  BG Simplification    : 0.03
% 3.17/1.47  Subsumption          : 0.07
% 3.17/1.47  Abstraction          : 0.02
% 3.17/1.47  MUC search           : 0.00
% 3.17/1.47  Cooper               : 0.00
% 3.17/1.47  Total                : 0.69
% 3.17/1.47  Index Insertion      : 0.00
% 3.17/1.47  Index Deletion       : 0.00
% 3.17/1.47  Index Matching       : 0.00
% 3.17/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
