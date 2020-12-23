%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 125 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    ! [A_58,B_59] :
      ( v1_relat_1(k7_relat_1(A_58,B_59))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    r2_hidden('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [C_35,A_20] :
      ( r2_hidden(k4_tarski(C_35,'#skF_8'(A_20,k1_relat_1(A_20),C_35)),A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    ! [C_86,A_87,B_88] :
      ( k1_funct_1(C_86,A_87) = B_88
      | ~ r2_hidden(k4_tarski(A_87,B_88),C_86)
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_202,plain,(
    ! [A_113,C_114] :
      ( '#skF_8'(A_113,k1_relat_1(A_113),C_114) = k1_funct_1(A_113,C_114)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113)
      | ~ r2_hidden(C_114,k1_relat_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_20,c_90])).

tff(c_221,plain,
    ( '#skF_8'('#skF_15',k1_relat_1('#skF_15'),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_60,c_202])).

tff(c_230,plain,(
    '#skF_8'('#skF_15',k1_relat_1('#skF_15'),'#skF_13') = k1_funct_1('#skF_15','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_221])).

tff(c_264,plain,
    ( r2_hidden(k4_tarski('#skF_13',k1_funct_1('#skF_15','#skF_13')),'#skF_15')
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_20])).

tff(c_270,plain,(
    r2_hidden(k4_tarski('#skF_13',k1_funct_1('#skF_15','#skF_13')),'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_264])).

tff(c_576,plain,(
    ! [D_151,E_152,A_153,B_154] :
      ( r2_hidden(k4_tarski(D_151,E_152),k7_relat_1(A_153,B_154))
      | ~ r2_hidden(k4_tarski(D_151,E_152),A_153)
      | ~ r2_hidden(D_151,B_154)
      | ~ v1_relat_1(k7_relat_1(A_153,B_154))
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [C_54,A_39,D_57] :
      ( r2_hidden(C_54,k2_relat_1(A_39))
      | ~ r2_hidden(k4_tarski(D_57,C_54),A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_746,plain,(
    ! [E_166,A_167,B_168,D_169] :
      ( r2_hidden(E_166,k2_relat_1(k7_relat_1(A_167,B_168)))
      | ~ r2_hidden(k4_tarski(D_169,E_166),A_167)
      | ~ r2_hidden(D_169,B_168)
      | ~ v1_relat_1(k7_relat_1(A_167,B_168))
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_576,c_34])).

tff(c_759,plain,(
    ! [B_168] :
      ( r2_hidden(k1_funct_1('#skF_15','#skF_13'),k2_relat_1(k7_relat_1('#skF_15',B_168)))
      | ~ r2_hidden('#skF_13',B_168)
      | ~ v1_relat_1(k7_relat_1('#skF_15',B_168))
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_270,c_746])).

tff(c_780,plain,(
    ! [B_170] :
      ( r2_hidden(k1_funct_1('#skF_15','#skF_13'),k2_relat_1(k7_relat_1('#skF_15',B_170)))
      | ~ r2_hidden('#skF_13',B_170)
      | ~ v1_relat_1(k7_relat_1('#skF_15',B_170)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_759])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_15','#skF_13'),k2_relat_1(k7_relat_1('#skF_15','#skF_14'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_783,plain,
    ( ~ r2_hidden('#skF_13','#skF_14')
    | ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(resolution,[status(thm)],[c_780,c_56])).

tff(c_786,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_783])).

tff(c_789,plain,
    ( ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_46,c_786])).

tff(c_793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n007.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 14:17:21 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5
% 2.80/1.44  
% 2.80/1.44  %Foreground sorts:
% 2.80/1.44  
% 2.80/1.44  
% 2.80/1.44  %Background operators:
% 2.80/1.44  
% 2.80/1.44  
% 2.80/1.44  %Foreground operators:
% 2.80/1.44  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 2.80/1.44  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.80/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.80/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.44  tff('#skF_15', type, '#skF_15': $i).
% 2.80/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.80/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.80/1.44  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.80/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.44  tff('#skF_14', type, '#skF_14': $i).
% 2.80/1.44  tff('#skF_13', type, '#skF_13': $i).
% 2.80/1.44  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.80/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.80/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.44  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.80/1.44  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.80/1.44  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.80/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.44  
% 2.80/1.45  tff(f_92, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 2.80/1.45  tff(f_63, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.80/1.45  tff(f_47, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.80/1.45  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.80/1.45  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 2.80/1.45  tff(f_55, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.80/1.45  tff(c_64, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.45  tff(c_62, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.45  tff(c_46, plain, (![A_58, B_59]: (v1_relat_1(k7_relat_1(A_58, B_59)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.80/1.45  tff(c_58, plain, (r2_hidden('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.45  tff(c_60, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.45  tff(c_20, plain, (![C_35, A_20]: (r2_hidden(k4_tarski(C_35, '#skF_8'(A_20, k1_relat_1(A_20), C_35)), A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.45  tff(c_90, plain, (![C_86, A_87, B_88]: (k1_funct_1(C_86, A_87)=B_88 | ~r2_hidden(k4_tarski(A_87, B_88), C_86) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.45  tff(c_202, plain, (![A_113, C_114]: ('#skF_8'(A_113, k1_relat_1(A_113), C_114)=k1_funct_1(A_113, C_114) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113) | ~r2_hidden(C_114, k1_relat_1(A_113)))), inference(resolution, [status(thm)], [c_20, c_90])).
% 2.80/1.45  tff(c_221, plain, ('#skF_8'('#skF_15', k1_relat_1('#skF_15'), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_60, c_202])).
% 2.80/1.45  tff(c_230, plain, ('#skF_8'('#skF_15', k1_relat_1('#skF_15'), '#skF_13')=k1_funct_1('#skF_15', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_221])).
% 2.80/1.45  tff(c_264, plain, (r2_hidden(k4_tarski('#skF_13', k1_funct_1('#skF_15', '#skF_13')), '#skF_15') | ~r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_20])).
% 2.80/1.45  tff(c_270, plain, (r2_hidden(k4_tarski('#skF_13', k1_funct_1('#skF_15', '#skF_13')), '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_264])).
% 2.80/1.45  tff(c_576, plain, (![D_151, E_152, A_153, B_154]: (r2_hidden(k4_tarski(D_151, E_152), k7_relat_1(A_153, B_154)) | ~r2_hidden(k4_tarski(D_151, E_152), A_153) | ~r2_hidden(D_151, B_154) | ~v1_relat_1(k7_relat_1(A_153, B_154)) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.45  tff(c_34, plain, (![C_54, A_39, D_57]: (r2_hidden(C_54, k2_relat_1(A_39)) | ~r2_hidden(k4_tarski(D_57, C_54), A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.45  tff(c_746, plain, (![E_166, A_167, B_168, D_169]: (r2_hidden(E_166, k2_relat_1(k7_relat_1(A_167, B_168))) | ~r2_hidden(k4_tarski(D_169, E_166), A_167) | ~r2_hidden(D_169, B_168) | ~v1_relat_1(k7_relat_1(A_167, B_168)) | ~v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_576, c_34])).
% 2.80/1.45  tff(c_759, plain, (![B_168]: (r2_hidden(k1_funct_1('#skF_15', '#skF_13'), k2_relat_1(k7_relat_1('#skF_15', B_168))) | ~r2_hidden('#skF_13', B_168) | ~v1_relat_1(k7_relat_1('#skF_15', B_168)) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_270, c_746])).
% 2.80/1.45  tff(c_780, plain, (![B_170]: (r2_hidden(k1_funct_1('#skF_15', '#skF_13'), k2_relat_1(k7_relat_1('#skF_15', B_170))) | ~r2_hidden('#skF_13', B_170) | ~v1_relat_1(k7_relat_1('#skF_15', B_170)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_759])).
% 2.80/1.45  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_15', '#skF_13'), k2_relat_1(k7_relat_1('#skF_15', '#skF_14')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.45  tff(c_783, plain, (~r2_hidden('#skF_13', '#skF_14') | ~v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(resolution, [status(thm)], [c_780, c_56])).
% 2.80/1.45  tff(c_786, plain, (~v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_783])).
% 2.80/1.45  tff(c_789, plain, (~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_46, c_786])).
% 2.80/1.45  tff(c_793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_789])).
% 2.80/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.45  
% 2.80/1.45  Inference rules
% 2.80/1.45  ----------------------
% 2.80/1.45  #Ref     : 0
% 2.80/1.45  #Sup     : 160
% 2.80/1.45  #Fact    : 0
% 2.80/1.45  #Define  : 0
% 2.80/1.45  #Split   : 0
% 2.80/1.45  #Chain   : 0
% 2.80/1.45  #Close   : 0
% 2.80/1.45  
% 2.80/1.45  Ordering : KBO
% 2.80/1.45  
% 2.80/1.45  Simplification rules
% 2.80/1.45  ----------------------
% 2.80/1.45  #Subsume      : 9
% 2.80/1.45  #Demod        : 14
% 2.80/1.45  #Tautology    : 35
% 2.80/1.45  #SimpNegUnit  : 0
% 2.80/1.45  #BackRed      : 0
% 2.80/1.45  
% 2.80/1.45  #Partial instantiations: 0
% 2.80/1.45  #Strategies tried      : 1
% 2.80/1.45  
% 2.80/1.45  Timing (in seconds)
% 2.80/1.45  ----------------------
% 2.80/1.45  Preprocessing        : 0.32
% 2.80/1.45  Parsing              : 0.16
% 2.80/1.45  CNF conversion       : 0.03
% 2.80/1.45  Main loop            : 0.38
% 2.80/1.45  Inferencing          : 0.16
% 2.80/1.45  Reduction            : 0.10
% 2.80/1.45  Demodulation         : 0.07
% 2.80/1.45  BG Simplification    : 0.03
% 2.80/1.45  Subsumption          : 0.08
% 2.80/1.45  Abstraction          : 0.02
% 2.80/1.45  MUC search           : 0.00
% 2.80/1.45  Cooper               : 0.00
% 2.80/1.45  Total                : 0.72
% 2.80/1.45  Index Insertion      : 0.00
% 2.80/1.45  Index Deletion       : 0.00
% 2.80/1.45  Index Matching       : 0.00
% 2.80/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
