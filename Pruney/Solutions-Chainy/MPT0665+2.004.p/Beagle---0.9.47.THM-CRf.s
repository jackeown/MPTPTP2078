%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:14 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 124 expanded)
%              Number of leaves         :   32 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 338 expanded)
%              Number of equality atoms :    6 (  19 expanded)
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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_62,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_62,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [A_79,B_80] :
      ( v1_funct_1(k7_relat_1(A_79,B_80))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,(
    r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    ! [A_79,B_80] :
      ( v1_relat_1(k7_relat_1(A_79,B_80))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_58,plain,(
    r2_hidden('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_76,plain,(
    ! [C_100,B_101,A_102] :
      ( k1_funct_1(k7_relat_1(C_100,B_101),A_102) = k1_funct_1(C_100,A_102)
      | ~ r2_hidden(A_102,B_101)
      | ~ v1_funct_1(C_100)
      | ~ v1_relat_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_39,D_78] :
      ( r2_hidden(k1_funct_1(A_39,D_78),k2_relat_1(A_39))
      | ~ r2_hidden(D_78,k1_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2152,plain,(
    ! [C_253,A_254,B_255] :
      ( r2_hidden(k1_funct_1(C_253,A_254),k2_relat_1(k7_relat_1(C_253,B_255)))
      | ~ r2_hidden(A_254,k1_relat_1(k7_relat_1(C_253,B_255)))
      | ~ v1_funct_1(k7_relat_1(C_253,B_255))
      | ~ v1_relat_1(k7_relat_1(C_253,B_255))
      | ~ r2_hidden(A_254,B_255)
      | ~ v1_funct_1(C_253)
      | ~ v1_relat_1(C_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_32])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_15','#skF_13'),k2_relat_1(k7_relat_1('#skF_15','#skF_14'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2155,plain,
    ( ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14')))
    | ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ r2_hidden('#skF_13','#skF_14')
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_2152,c_56])).

tff(c_2188,plain,
    ( ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14')))
    | ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_2155])).

tff(c_2189,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_2188])).

tff(c_2192,plain,
    ( ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_52,c_2189])).

tff(c_2196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2192])).

tff(c_2198,plain,(
    v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(splitRight,[status(thm)],[c_2188])).

tff(c_20,plain,(
    ! [C_35,A_20] :
      ( r2_hidden(k4_tarski(C_35,'#skF_8'(A_20,k1_relat_1(A_20),C_35)),A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_249,plain,(
    ! [D_135,E_136,A_137,B_138] :
      ( r2_hidden(k4_tarski(D_135,E_136),k7_relat_1(A_137,B_138))
      | ~ r2_hidden(k4_tarski(D_135,E_136),A_137)
      | ~ r2_hidden(D_135,B_138)
      | ~ v1_relat_1(k7_relat_1(A_137,B_138))
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k1_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(C_35,D_38),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_266,plain,(
    ! [D_139,A_140,B_141,E_142] :
      ( r2_hidden(D_139,k1_relat_1(k7_relat_1(A_140,B_141)))
      | ~ r2_hidden(k4_tarski(D_139,E_142),A_140)
      | ~ r2_hidden(D_139,B_141)
      | ~ v1_relat_1(k7_relat_1(A_140,B_141))
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_249,c_22])).

tff(c_278,plain,(
    ! [C_35,A_20,B_141] :
      ( r2_hidden(C_35,k1_relat_1(k7_relat_1(A_20,B_141)))
      | ~ r2_hidden(C_35,B_141)
      | ~ v1_relat_1(k7_relat_1(A_20,B_141))
      | ~ v1_relat_1(A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_20,c_266])).

tff(c_2197,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14'))) ),
    inference(splitRight,[status(thm)],[c_2188])).

tff(c_2204,plain,(
    ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14'))) ),
    inference(splitLeft,[status(thm)],[c_2197])).

tff(c_2207,plain,
    ( ~ r2_hidden('#skF_13','#skF_14')
    | ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ v1_relat_1('#skF_15')
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_278,c_2204])).

tff(c_2211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_2198,c_58,c_2207])).

tff(c_2212,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(splitRight,[status(thm)],[c_2197])).

tff(c_2216,plain,
    ( ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_50,c_2212])).

tff(c_2220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.10  
% 6.16/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.10  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5
% 6.16/2.10  
% 6.16/2.10  %Foreground sorts:
% 6.16/2.10  
% 6.16/2.10  
% 6.16/2.10  %Background operators:
% 6.16/2.10  
% 6.16/2.10  
% 6.16/2.10  %Foreground operators:
% 6.16/2.10  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 6.16/2.10  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.16/2.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.16/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.16/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.16/2.10  tff('#skF_15', type, '#skF_15': $i).
% 6.16/2.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.16/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.16/2.10  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 6.16/2.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.16/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.16/2.10  tff('#skF_14', type, '#skF_14': $i).
% 6.16/2.10  tff('#skF_13', type, '#skF_13': $i).
% 6.16/2.10  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 6.16/2.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.16/2.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.16/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.16/2.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.16/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.11  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 6.16/2.11  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.16/2.11  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 6.16/2.11  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.16/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.16/2.11  
% 6.16/2.12  tff(f_89, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 6.16/2.12  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 6.16/2.12  tff(f_78, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 6.16/2.12  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 6.16/2.12  tff(f_47, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 6.16/2.12  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 6.16/2.12  tff(c_64, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.16/2.12  tff(c_62, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.16/2.12  tff(c_50, plain, (![A_79, B_80]: (v1_funct_1(k7_relat_1(A_79, B_80)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.16/2.12  tff(c_60, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.16/2.12  tff(c_52, plain, (![A_79, B_80]: (v1_relat_1(k7_relat_1(A_79, B_80)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.16/2.12  tff(c_58, plain, (r2_hidden('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.16/2.12  tff(c_76, plain, (![C_100, B_101, A_102]: (k1_funct_1(k7_relat_1(C_100, B_101), A_102)=k1_funct_1(C_100, A_102) | ~r2_hidden(A_102, B_101) | ~v1_funct_1(C_100) | ~v1_relat_1(C_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.16/2.12  tff(c_32, plain, (![A_39, D_78]: (r2_hidden(k1_funct_1(A_39, D_78), k2_relat_1(A_39)) | ~r2_hidden(D_78, k1_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.16/2.12  tff(c_2152, plain, (![C_253, A_254, B_255]: (r2_hidden(k1_funct_1(C_253, A_254), k2_relat_1(k7_relat_1(C_253, B_255))) | ~r2_hidden(A_254, k1_relat_1(k7_relat_1(C_253, B_255))) | ~v1_funct_1(k7_relat_1(C_253, B_255)) | ~v1_relat_1(k7_relat_1(C_253, B_255)) | ~r2_hidden(A_254, B_255) | ~v1_funct_1(C_253) | ~v1_relat_1(C_253))), inference(superposition, [status(thm), theory('equality')], [c_76, c_32])).
% 6.16/2.12  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_15', '#skF_13'), k2_relat_1(k7_relat_1('#skF_15', '#skF_14')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.16/2.12  tff(c_2155, plain, (~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14'))) | ~v1_funct_1(k7_relat_1('#skF_15', '#skF_14')) | ~v1_relat_1(k7_relat_1('#skF_15', '#skF_14')) | ~r2_hidden('#skF_13', '#skF_14') | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_2152, c_56])).
% 6.16/2.12  tff(c_2188, plain, (~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14'))) | ~v1_funct_1(k7_relat_1('#skF_15', '#skF_14')) | ~v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_2155])).
% 6.16/2.12  tff(c_2189, plain, (~v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(splitLeft, [status(thm)], [c_2188])).
% 6.16/2.12  tff(c_2192, plain, (~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_52, c_2189])).
% 6.16/2.12  tff(c_2196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2192])).
% 6.16/2.12  tff(c_2198, plain, (v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(splitRight, [status(thm)], [c_2188])).
% 6.16/2.12  tff(c_20, plain, (![C_35, A_20]: (r2_hidden(k4_tarski(C_35, '#skF_8'(A_20, k1_relat_1(A_20), C_35)), A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.16/2.12  tff(c_249, plain, (![D_135, E_136, A_137, B_138]: (r2_hidden(k4_tarski(D_135, E_136), k7_relat_1(A_137, B_138)) | ~r2_hidden(k4_tarski(D_135, E_136), A_137) | ~r2_hidden(D_135, B_138) | ~v1_relat_1(k7_relat_1(A_137, B_138)) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.16/2.12  tff(c_22, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k1_relat_1(A_20)) | ~r2_hidden(k4_tarski(C_35, D_38), A_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.16/2.12  tff(c_266, plain, (![D_139, A_140, B_141, E_142]: (r2_hidden(D_139, k1_relat_1(k7_relat_1(A_140, B_141))) | ~r2_hidden(k4_tarski(D_139, E_142), A_140) | ~r2_hidden(D_139, B_141) | ~v1_relat_1(k7_relat_1(A_140, B_141)) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_249, c_22])).
% 6.16/2.12  tff(c_278, plain, (![C_35, A_20, B_141]: (r2_hidden(C_35, k1_relat_1(k7_relat_1(A_20, B_141))) | ~r2_hidden(C_35, B_141) | ~v1_relat_1(k7_relat_1(A_20, B_141)) | ~v1_relat_1(A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(resolution, [status(thm)], [c_20, c_266])).
% 6.16/2.12  tff(c_2197, plain, (~v1_funct_1(k7_relat_1('#skF_15', '#skF_14')) | ~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14')))), inference(splitRight, [status(thm)], [c_2188])).
% 6.16/2.12  tff(c_2204, plain, (~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14')))), inference(splitLeft, [status(thm)], [c_2197])).
% 6.16/2.12  tff(c_2207, plain, (~r2_hidden('#skF_13', '#skF_14') | ~v1_relat_1(k7_relat_1('#skF_15', '#skF_14')) | ~v1_relat_1('#skF_15') | ~r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_278, c_2204])).
% 6.16/2.12  tff(c_2211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_2198, c_58, c_2207])).
% 6.16/2.12  tff(c_2212, plain, (~v1_funct_1(k7_relat_1('#skF_15', '#skF_14'))), inference(splitRight, [status(thm)], [c_2197])).
% 6.16/2.12  tff(c_2216, plain, (~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_50, c_2212])).
% 6.16/2.12  tff(c_2220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2216])).
% 6.16/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.12  
% 6.16/2.12  Inference rules
% 6.16/2.12  ----------------------
% 6.16/2.12  #Ref     : 0
% 6.16/2.12  #Sup     : 545
% 6.16/2.12  #Fact    : 0
% 6.16/2.12  #Define  : 0
% 6.16/2.12  #Split   : 2
% 6.16/2.12  #Chain   : 0
% 6.16/2.12  #Close   : 0
% 6.16/2.12  
% 6.16/2.12  Ordering : KBO
% 6.16/2.12  
% 6.16/2.12  Simplification rules
% 6.16/2.12  ----------------------
% 6.16/2.12  #Subsume      : 79
% 6.16/2.12  #Demod        : 12
% 6.16/2.12  #Tautology    : 108
% 6.16/2.12  #SimpNegUnit  : 0
% 6.16/2.12  #BackRed      : 0
% 6.16/2.12  
% 6.16/2.12  #Partial instantiations: 0
% 6.16/2.12  #Strategies tried      : 1
% 6.16/2.12  
% 6.16/2.12  Timing (in seconds)
% 6.16/2.12  ----------------------
% 6.31/2.12  Preprocessing        : 0.33
% 6.31/2.12  Parsing              : 0.16
% 6.31/2.12  CNF conversion       : 0.03
% 6.31/2.12  Main loop            : 1.03
% 6.31/2.12  Inferencing          : 0.33
% 6.31/2.12  Reduction            : 0.23
% 6.31/2.12  Demodulation         : 0.16
% 6.31/2.12  BG Simplification    : 0.05
% 6.31/2.12  Subsumption          : 0.33
% 6.31/2.12  Abstraction          : 0.06
% 6.31/2.12  MUC search           : 0.00
% 6.31/2.12  Cooper               : 0.00
% 6.31/2.12  Total                : 1.39
% 6.31/2.12  Index Insertion      : 0.00
% 6.31/2.12  Index Deletion       : 0.00
% 6.31/2.12  Index Matching       : 0.00
% 6.31/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
