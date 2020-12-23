%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 120 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 362 expanded)
%              Number of equality atoms :   19 (  98 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_119,plain,(
    ! [A_38,D_39] :
      ( k1_funct_1(k2_funct_1(A_38),k1_funct_1(A_38,D_39)) = D_39
      | ~ r2_hidden(D_39,k1_relat_1(A_38))
      | ~ v1_funct_1(k2_funct_1(A_38))
      | ~ v1_relat_1(k2_funct_1(A_38))
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_47,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_137,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_47])).

tff(c_154,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_137])).

tff(c_157,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_160,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_157])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_160])).

tff(c_165,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_176,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_176])).

tff(c_182,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_210,plain,(
    ! [B_46,C_47,A_48] :
      ( k1_funct_1(k5_relat_1(B_46,C_47),A_48) = k1_funct_1(C_47,k1_funct_1(B_46,A_48))
      | ~ r2_hidden(A_48,k1_relat_1(B_46))
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_214,plain,(
    ! [C_47] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_47),'#skF_5') = k1_funct_1(C_47,k1_funct_1('#skF_6','#skF_5'))
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_210])).

tff(c_218,plain,(
    ! [C_49] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_49),'#skF_5') = k1_funct_1(C_49,k1_funct_1('#skF_6','#skF_5'))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_214])).

tff(c_181,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_227,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5'
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_181])).

tff(c_233,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_227])).

tff(c_235,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_238,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_235])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_238])).

tff(c_243,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_247,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_243])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.36  
% 2.25/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.37  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.25/1.37  
% 2.25/1.37  %Foreground sorts:
% 2.25/1.37  
% 2.25/1.37  
% 2.25/1.37  %Background operators:
% 2.25/1.37  
% 2.25/1.37  
% 2.25/1.37  %Foreground operators:
% 2.25/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.25/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.25/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.25/1.37  
% 2.50/1.38  tff(f_91, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 2.50/1.38  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.50/1.38  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 2.50/1.38  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.50/1.38  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.50/1.38  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.50/1.38  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.38  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.38  tff(c_40, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.50/1.38  tff(c_38, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.50/1.38  tff(c_119, plain, (![A_38, D_39]: (k1_funct_1(k2_funct_1(A_38), k1_funct_1(A_38, D_39))=D_39 | ~r2_hidden(D_39, k1_relat_1(A_38)) | ~v1_funct_1(k2_funct_1(A_38)) | ~v1_relat_1(k2_funct_1(A_38)) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.50/1.38  tff(c_36, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.50/1.38  tff(c_47, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_36])).
% 2.50/1.38  tff(c_137, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_119, c_47])).
% 2.50/1.38  tff(c_154, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_137])).
% 2.50/1.38  tff(c_157, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_154])).
% 2.50/1.38  tff(c_160, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_157])).
% 2.50/1.38  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_160])).
% 2.50/1.38  tff(c_165, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_154])).
% 2.50/1.38  tff(c_176, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_165])).
% 2.50/1.38  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_176])).
% 2.50/1.38  tff(c_182, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 2.50/1.38  tff(c_210, plain, (![B_46, C_47, A_48]: (k1_funct_1(k5_relat_1(B_46, C_47), A_48)=k1_funct_1(C_47, k1_funct_1(B_46, A_48)) | ~r2_hidden(A_48, k1_relat_1(B_46)) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.38  tff(c_214, plain, (![C_47]: (k1_funct_1(k5_relat_1('#skF_6', C_47), '#skF_5')=k1_funct_1(C_47, k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_210])).
% 2.50/1.38  tff(c_218, plain, (![C_49]: (k1_funct_1(k5_relat_1('#skF_6', C_49), '#skF_5')=k1_funct_1(C_49, k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_214])).
% 2.50/1.38  tff(c_181, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 2.50/1.38  tff(c_227, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5' | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_181])).
% 2.50/1.38  tff(c_233, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_227])).
% 2.50/1.38  tff(c_235, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_233])).
% 2.50/1.38  tff(c_238, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_235])).
% 2.50/1.38  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_238])).
% 2.50/1.38  tff(c_243, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_233])).
% 2.50/1.38  tff(c_247, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_243])).
% 2.50/1.38  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_247])).
% 2.50/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  Inference rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Ref     : 0
% 2.50/1.38  #Sup     : 45
% 2.50/1.38  #Fact    : 0
% 2.50/1.38  #Define  : 0
% 2.50/1.38  #Split   : 3
% 2.50/1.38  #Chain   : 0
% 2.50/1.38  #Close   : 0
% 2.50/1.38  
% 2.50/1.38  Ordering : KBO
% 2.50/1.38  
% 2.50/1.38  Simplification rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Subsume      : 4
% 2.50/1.38  #Demod        : 21
% 2.50/1.38  #Tautology    : 18
% 2.50/1.38  #SimpNegUnit  : 0
% 2.50/1.38  #BackRed      : 0
% 2.50/1.38  
% 2.50/1.38  #Partial instantiations: 0
% 2.50/1.38  #Strategies tried      : 1
% 2.50/1.38  
% 2.50/1.38  Timing (in seconds)
% 2.50/1.38  ----------------------
% 2.50/1.38  Preprocessing        : 0.33
% 2.50/1.38  Parsing              : 0.17
% 2.50/1.38  CNF conversion       : 0.02
% 2.50/1.38  Main loop            : 0.23
% 2.50/1.38  Inferencing          : 0.08
% 2.50/1.38  Reduction            : 0.06
% 2.50/1.38  Demodulation         : 0.05
% 2.50/1.38  BG Simplification    : 0.02
% 2.50/1.38  Subsumption          : 0.05
% 2.50/1.38  Abstraction          : 0.01
% 2.50/1.38  MUC search           : 0.00
% 2.50/1.38  Cooper               : 0.00
% 2.50/1.38  Total                : 0.59
% 2.50/1.38  Index Insertion      : 0.00
% 2.50/1.38  Index Deletion       : 0.00
% 2.50/1.38  Index Matching       : 0.00
% 2.50/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
