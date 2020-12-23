%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:14 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 119 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_16 > #skF_14 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

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

tff(c_70,plain,(
    v1_relat_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    ! [A_58,B_59] :
      ( v1_relat_1(k7_relat_1(A_58,B_59))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    r2_hidden('#skF_14','#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    r2_hidden('#skF_14',k1_relat_1('#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_68,plain,(
    v1_funct_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [C_35,A_20] :
      ( r2_hidden(k4_tarski(C_35,'#skF_8'(A_20,k1_relat_1(A_20),C_35)),A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_320,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_funct_1(A_128,B_129) = C_130
      | ~ r2_hidden(k4_tarski(B_129,C_130),A_128)
      | ~ r2_hidden(B_129,k1_relat_1(A_128))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_353,plain,(
    ! [A_131,C_132] :
      ( '#skF_8'(A_131,k1_relat_1(A_131),C_132) = k1_funct_1(A_131,C_132)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131)
      | ~ r2_hidden(C_132,k1_relat_1(A_131)) ) ),
    inference(resolution,[status(thm)],[c_20,c_320])).

tff(c_384,plain,
    ( '#skF_8'('#skF_16',k1_relat_1('#skF_16'),'#skF_14') = k1_funct_1('#skF_16','#skF_14')
    | ~ v1_funct_1('#skF_16')
    | ~ v1_relat_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_66,c_353])).

tff(c_398,plain,(
    '#skF_8'('#skF_16',k1_relat_1('#skF_16'),'#skF_14') = k1_funct_1('#skF_16','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_384])).

tff(c_405,plain,
    ( r2_hidden(k4_tarski('#skF_14',k1_funct_1('#skF_16','#skF_14')),'#skF_16')
    | ~ r2_hidden('#skF_14',k1_relat_1('#skF_16')) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_20])).

tff(c_411,plain,(
    r2_hidden(k4_tarski('#skF_14',k1_funct_1('#skF_16','#skF_14')),'#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_405])).

tff(c_1325,plain,(
    ! [D_189,E_190,A_191,B_192] :
      ( r2_hidden(k4_tarski(D_189,E_190),k7_relat_1(A_191,B_192))
      | ~ r2_hidden(k4_tarski(D_189,E_190),A_191)
      | ~ r2_hidden(D_189,B_192)
      | ~ v1_relat_1(k7_relat_1(A_191,B_192))
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [C_54,A_39,D_57] :
      ( r2_hidden(C_54,k2_relat_1(A_39))
      | ~ r2_hidden(k4_tarski(D_57,C_54),A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1681,plain,(
    ! [E_221,A_222,B_223,D_224] :
      ( r2_hidden(E_221,k2_relat_1(k7_relat_1(A_222,B_223)))
      | ~ r2_hidden(k4_tarski(D_224,E_221),A_222)
      | ~ r2_hidden(D_224,B_223)
      | ~ v1_relat_1(k7_relat_1(A_222,B_223))
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_1325,c_34])).

tff(c_1713,plain,(
    ! [B_223] :
      ( r2_hidden(k1_funct_1('#skF_16','#skF_14'),k2_relat_1(k7_relat_1('#skF_16',B_223)))
      | ~ r2_hidden('#skF_14',B_223)
      | ~ v1_relat_1(k7_relat_1('#skF_16',B_223))
      | ~ v1_relat_1('#skF_16') ) ),
    inference(resolution,[status(thm)],[c_411,c_1681])).

tff(c_1794,plain,(
    ! [B_228] :
      ( r2_hidden(k1_funct_1('#skF_16','#skF_14'),k2_relat_1(k7_relat_1('#skF_16',B_228)))
      | ~ r2_hidden('#skF_14',B_228)
      | ~ v1_relat_1(k7_relat_1('#skF_16',B_228)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1713])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_16','#skF_14'),k2_relat_1(k7_relat_1('#skF_16','#skF_15'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1799,plain,
    ( ~ r2_hidden('#skF_14','#skF_15')
    | ~ v1_relat_1(k7_relat_1('#skF_16','#skF_15')) ),
    inference(resolution,[status(thm)],[c_1794,c_62])).

tff(c_1803,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_16','#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1799])).

tff(c_1806,plain,(
    ~ v1_relat_1('#skF_16') ),
    inference(resolution,[status(thm)],[c_44,c_1803])).

tff(c_1810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.83  
% 4.46/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.83  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_16 > #skF_14 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5
% 4.46/1.83  
% 4.46/1.83  %Foreground sorts:
% 4.46/1.83  
% 4.46/1.83  
% 4.46/1.83  %Background operators:
% 4.46/1.83  
% 4.46/1.83  
% 4.46/1.83  %Foreground operators:
% 4.46/1.83  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 4.46/1.83  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 4.46/1.83  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.46/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.46/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.46/1.83  tff('#skF_15', type, '#skF_15': $i).
% 4.46/1.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.46/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.46/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.83  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 4.46/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.46/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.46/1.83  tff('#skF_16', type, '#skF_16': $i).
% 4.46/1.83  tff('#skF_14', type, '#skF_14': $i).
% 4.46/1.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.46/1.83  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 4.46/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.46/1.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.46/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.83  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.46/1.83  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.46/1.83  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 4.46/1.83  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.46/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.46/1.83  
% 4.46/1.84  tff(f_99, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 4.46/1.84  tff(f_59, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.46/1.84  tff(f_47, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.46/1.84  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 4.46/1.84  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 4.46/1.84  tff(f_55, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 4.46/1.84  tff(c_70, plain, (v1_relat_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.46/1.84  tff(c_44, plain, (![A_58, B_59]: (v1_relat_1(k7_relat_1(A_58, B_59)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.46/1.84  tff(c_64, plain, (r2_hidden('#skF_14', '#skF_15')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.46/1.84  tff(c_66, plain, (r2_hidden('#skF_14', k1_relat_1('#skF_16'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.46/1.84  tff(c_68, plain, (v1_funct_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.46/1.84  tff(c_20, plain, (![C_35, A_20]: (r2_hidden(k4_tarski(C_35, '#skF_8'(A_20, k1_relat_1(A_20), C_35)), A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.46/1.84  tff(c_320, plain, (![A_128, B_129, C_130]: (k1_funct_1(A_128, B_129)=C_130 | ~r2_hidden(k4_tarski(B_129, C_130), A_128) | ~r2_hidden(B_129, k1_relat_1(A_128)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.46/1.84  tff(c_353, plain, (![A_131, C_132]: ('#skF_8'(A_131, k1_relat_1(A_131), C_132)=k1_funct_1(A_131, C_132) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131) | ~r2_hidden(C_132, k1_relat_1(A_131)))), inference(resolution, [status(thm)], [c_20, c_320])).
% 4.46/1.84  tff(c_384, plain, ('#skF_8'('#skF_16', k1_relat_1('#skF_16'), '#skF_14')=k1_funct_1('#skF_16', '#skF_14') | ~v1_funct_1('#skF_16') | ~v1_relat_1('#skF_16')), inference(resolution, [status(thm)], [c_66, c_353])).
% 4.46/1.84  tff(c_398, plain, ('#skF_8'('#skF_16', k1_relat_1('#skF_16'), '#skF_14')=k1_funct_1('#skF_16', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_384])).
% 4.46/1.84  tff(c_405, plain, (r2_hidden(k4_tarski('#skF_14', k1_funct_1('#skF_16', '#skF_14')), '#skF_16') | ~r2_hidden('#skF_14', k1_relat_1('#skF_16'))), inference(superposition, [status(thm), theory('equality')], [c_398, c_20])).
% 4.46/1.84  tff(c_411, plain, (r2_hidden(k4_tarski('#skF_14', k1_funct_1('#skF_16', '#skF_14')), '#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_405])).
% 4.46/1.84  tff(c_1325, plain, (![D_189, E_190, A_191, B_192]: (r2_hidden(k4_tarski(D_189, E_190), k7_relat_1(A_191, B_192)) | ~r2_hidden(k4_tarski(D_189, E_190), A_191) | ~r2_hidden(D_189, B_192) | ~v1_relat_1(k7_relat_1(A_191, B_192)) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.46/1.84  tff(c_34, plain, (![C_54, A_39, D_57]: (r2_hidden(C_54, k2_relat_1(A_39)) | ~r2_hidden(k4_tarski(D_57, C_54), A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.46/1.84  tff(c_1681, plain, (![E_221, A_222, B_223, D_224]: (r2_hidden(E_221, k2_relat_1(k7_relat_1(A_222, B_223))) | ~r2_hidden(k4_tarski(D_224, E_221), A_222) | ~r2_hidden(D_224, B_223) | ~v1_relat_1(k7_relat_1(A_222, B_223)) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_1325, c_34])).
% 4.46/1.84  tff(c_1713, plain, (![B_223]: (r2_hidden(k1_funct_1('#skF_16', '#skF_14'), k2_relat_1(k7_relat_1('#skF_16', B_223))) | ~r2_hidden('#skF_14', B_223) | ~v1_relat_1(k7_relat_1('#skF_16', B_223)) | ~v1_relat_1('#skF_16'))), inference(resolution, [status(thm)], [c_411, c_1681])).
% 4.46/1.84  tff(c_1794, plain, (![B_228]: (r2_hidden(k1_funct_1('#skF_16', '#skF_14'), k2_relat_1(k7_relat_1('#skF_16', B_228))) | ~r2_hidden('#skF_14', B_228) | ~v1_relat_1(k7_relat_1('#skF_16', B_228)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1713])).
% 4.46/1.84  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_16', '#skF_14'), k2_relat_1(k7_relat_1('#skF_16', '#skF_15')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.46/1.84  tff(c_1799, plain, (~r2_hidden('#skF_14', '#skF_15') | ~v1_relat_1(k7_relat_1('#skF_16', '#skF_15'))), inference(resolution, [status(thm)], [c_1794, c_62])).
% 4.46/1.84  tff(c_1803, plain, (~v1_relat_1(k7_relat_1('#skF_16', '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1799])).
% 4.46/1.84  tff(c_1806, plain, (~v1_relat_1('#skF_16')), inference(resolution, [status(thm)], [c_44, c_1803])).
% 4.46/1.84  tff(c_1810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1806])).
% 4.46/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.84  
% 4.46/1.84  Inference rules
% 4.46/1.84  ----------------------
% 4.46/1.84  #Ref     : 0
% 4.46/1.84  #Sup     : 401
% 4.46/1.84  #Fact    : 0
% 4.46/1.84  #Define  : 0
% 4.46/1.84  #Split   : 0
% 4.46/1.84  #Chain   : 0
% 4.46/1.84  #Close   : 0
% 4.46/1.84  
% 4.46/1.84  Ordering : KBO
% 4.46/1.84  
% 4.46/1.84  Simplification rules
% 4.46/1.84  ----------------------
% 4.46/1.84  #Subsume      : 14
% 4.46/1.84  #Demod        : 25
% 4.46/1.84  #Tautology    : 70
% 4.46/1.84  #SimpNegUnit  : 0
% 4.46/1.84  #BackRed      : 0
% 4.46/1.84  
% 4.46/1.84  #Partial instantiations: 0
% 4.46/1.84  #Strategies tried      : 1
% 4.46/1.84  
% 4.46/1.84  Timing (in seconds)
% 4.46/1.84  ----------------------
% 4.55/1.85  Preprocessing        : 0.33
% 4.55/1.85  Parsing              : 0.17
% 4.55/1.85  CNF conversion       : 0.03
% 4.55/1.85  Main loop            : 0.75
% 4.55/1.85  Inferencing          : 0.28
% 4.55/1.85  Reduction            : 0.19
% 4.55/1.85  Demodulation         : 0.13
% 4.55/1.85  BG Simplification    : 0.04
% 4.55/1.85  Subsumption          : 0.18
% 4.55/1.85  Abstraction          : 0.04
% 4.55/1.85  MUC search           : 0.00
% 4.55/1.85  Cooper               : 0.00
% 4.55/1.85  Total                : 1.12
% 4.55/1.85  Index Insertion      : 0.00
% 4.55/1.85  Index Deletion       : 0.00
% 4.55/1.85  Index Matching       : 0.00
% 4.55/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
