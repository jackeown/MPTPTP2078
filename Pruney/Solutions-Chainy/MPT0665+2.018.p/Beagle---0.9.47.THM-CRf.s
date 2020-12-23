%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   45 (  93 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 255 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_48,axiom,(
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

tff(c_40,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_44,B_45] :
      ( v1_funct_1(k7_relat_1(A_44,B_45))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,k1_relat_1(k7_relat_1(C_3,B_2)))
      | ~ r2_hidden(A_1,k1_relat_1(C_3))
      | ~ r2_hidden(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k7_relat_1(A_44,B_45))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    ! [C_64,B_65,A_66] :
      ( k1_funct_1(k7_relat_1(C_64,B_65),A_66) = k1_funct_1(C_64,A_66)
      | ~ r2_hidden(A_66,B_65)
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_4,D_43] :
      ( r2_hidden(k1_funct_1(A_4,D_43),k2_relat_1(A_4))
      | ~ r2_hidden(D_43,k1_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_263,plain,(
    ! [C_102,A_103,B_104] :
      ( r2_hidden(k1_funct_1(C_102,A_103),k2_relat_1(k7_relat_1(C_102,B_104)))
      | ~ r2_hidden(A_103,k1_relat_1(k7_relat_1(C_102,B_104)))
      | ~ v1_funct_1(k7_relat_1(C_102,B_104))
      | ~ v1_relat_1(k7_relat_1(C_102,B_104))
      | ~ r2_hidden(A_103,B_104)
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_266,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_263,c_32])).

tff(c_278,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_266])).

tff(c_279,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_282,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_279])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_282])).

tff(c_287,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_289,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_292,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_289])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_36,c_292])).

tff(c_297,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_301,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_297])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.31  
% 2.36/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.32  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.52/1.32  
% 2.52/1.32  %Foreground sorts:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Background operators:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Foreground operators:
% 2.52/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.52/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.52/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.52/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.52/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.52/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.52/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.52/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.52/1.32  
% 2.52/1.33  tff(f_75, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 2.52/1.33  tff(f_56, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.52/1.33  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.52/1.33  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 2.52/1.33  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.52/1.33  tff(c_40, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.52/1.33  tff(c_38, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.52/1.33  tff(c_26, plain, (![A_44, B_45]: (v1_funct_1(k7_relat_1(A_44, B_45)) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.52/1.33  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.52/1.33  tff(c_36, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.52/1.33  tff(c_2, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, k1_relat_1(k7_relat_1(C_3, B_2))) | ~r2_hidden(A_1, k1_relat_1(C_3)) | ~r2_hidden(A_1, B_2) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.52/1.33  tff(c_28, plain, (![A_44, B_45]: (v1_relat_1(k7_relat_1(A_44, B_45)) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.52/1.33  tff(c_55, plain, (![C_64, B_65, A_66]: (k1_funct_1(k7_relat_1(C_64, B_65), A_66)=k1_funct_1(C_64, A_66) | ~r2_hidden(A_66, B_65) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.33  tff(c_8, plain, (![A_4, D_43]: (r2_hidden(k1_funct_1(A_4, D_43), k2_relat_1(A_4)) | ~r2_hidden(D_43, k1_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.52/1.33  tff(c_263, plain, (![C_102, A_103, B_104]: (r2_hidden(k1_funct_1(C_102, A_103), k2_relat_1(k7_relat_1(C_102, B_104))) | ~r2_hidden(A_103, k1_relat_1(k7_relat_1(C_102, B_104))) | ~v1_funct_1(k7_relat_1(C_102, B_104)) | ~v1_relat_1(k7_relat_1(C_102, B_104)) | ~r2_hidden(A_103, B_104) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102))), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 2.52/1.33  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.52/1.33  tff(c_266, plain, (~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))) | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_263, c_32])).
% 2.52/1.33  tff(c_278, plain, (~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))) | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_266])).
% 2.52/1.33  tff(c_279, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_278])).
% 2.52/1.33  tff(c_282, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_279])).
% 2.52/1.33  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_282])).
% 2.52/1.33  tff(c_287, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_278])).
% 2.52/1.33  tff(c_289, plain, (~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_287])).
% 2.52/1.33  tff(c_292, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2, c_289])).
% 2.52/1.33  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_36, c_292])).
% 2.52/1.33  tff(c_297, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_287])).
% 2.52/1.33  tff(c_301, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_297])).
% 2.52/1.33  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_301])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 55
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 2
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 1
% 2.52/1.33  #Demod        : 10
% 2.52/1.33  #Tautology    : 9
% 2.52/1.33  #SimpNegUnit  : 0
% 2.52/1.33  #BackRed      : 0
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.33  Preprocessing        : 0.29
% 2.52/1.33  Parsing              : 0.15
% 2.52/1.33  CNF conversion       : 0.03
% 2.52/1.33  Main loop            : 0.28
% 2.52/1.33  Inferencing          : 0.11
% 2.52/1.33  Reduction            : 0.07
% 2.52/1.33  Demodulation         : 0.05
% 2.52/1.33  BG Simplification    : 0.02
% 2.52/1.33  Subsumption          : 0.06
% 2.52/1.33  Abstraction          : 0.01
% 2.52/1.33  MUC search           : 0.00
% 2.52/1.33  Cooper               : 0.00
% 2.52/1.33  Total                : 0.60
% 2.52/1.33  Index Insertion      : 0.00
% 2.52/1.33  Index Deletion       : 0.00
% 2.52/1.33  Index Matching       : 0.00
% 2.52/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
