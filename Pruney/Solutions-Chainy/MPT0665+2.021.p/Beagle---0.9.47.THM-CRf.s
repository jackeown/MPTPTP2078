%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:17 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   41 (  89 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 249 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( v1_funct_1(k7_relat_1(A_4,B_5))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,k1_relat_1(k7_relat_1(C_3,B_2)))
      | ~ r2_hidden(A_1,k1_relat_1(C_3))
      | ~ r2_hidden(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [C_23,B_24,A_25] :
      ( k1_funct_1(k7_relat_1(C_23,B_24),A_25) = k1_funct_1(C_23,A_25)
      | ~ r2_hidden(A_25,B_24)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r2_hidden(k1_funct_1(B_7,A_6),k2_relat_1(B_7))
      | ~ r2_hidden(A_6,k1_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,(
    ! [C_29,A_30,B_31] :
      ( r2_hidden(k1_funct_1(C_29,A_30),k2_relat_1(k7_relat_1(C_29,B_31)))
      | ~ r2_hidden(A_30,k1_relat_1(k7_relat_1(C_29,B_31)))
      | ~ v1_funct_1(k7_relat_1(C_29,B_31))
      | ~ v1_relat_1(k7_relat_1(C_29,B_31))
      | ~ r2_hidden(A_30,B_31)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_16,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),k2_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r2_hidden('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_16])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_54])).

tff(c_61,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_64])).

tff(c_69,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_20,c_74])).

tff(c_79,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_83,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:10:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.74/1.17  
% 1.74/1.17  %Foreground sorts:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Background operators:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Foreground operators:
% 1.74/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.74/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.17  
% 1.98/1.18  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 1.98/1.18  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 1.98/1.18  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 1.98/1.18  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 1.98/1.18  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 1.98/1.18  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.18  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.18  tff(c_8, plain, (![A_4, B_5]: (v1_funct_1(k7_relat_1(A_4, B_5)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.18  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.18  tff(c_20, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.18  tff(c_2, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, k1_relat_1(k7_relat_1(C_3, B_2))) | ~r2_hidden(A_1, k1_relat_1(C_3)) | ~r2_hidden(A_1, B_2) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.18  tff(c_10, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.18  tff(c_30, plain, (![C_23, B_24, A_25]: (k1_funct_1(k7_relat_1(C_23, B_24), A_25)=k1_funct_1(C_23, A_25) | ~r2_hidden(A_25, B_24) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.18  tff(c_12, plain, (![B_7, A_6]: (r2_hidden(k1_funct_1(B_7, A_6), k2_relat_1(B_7)) | ~r2_hidden(A_6, k1_relat_1(B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.18  tff(c_51, plain, (![C_29, A_30, B_31]: (r2_hidden(k1_funct_1(C_29, A_30), k2_relat_1(k7_relat_1(C_29, B_31))) | ~r2_hidden(A_30, k1_relat_1(k7_relat_1(C_29, B_31))) | ~v1_funct_1(k7_relat_1(C_29, B_31)) | ~v1_relat_1(k7_relat_1(C_29, B_31)) | ~r2_hidden(A_30, B_31) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(superposition, [status(thm), theory('equality')], [c_30, c_12])).
% 1.98/1.18  tff(c_16, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k2_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.18  tff(c_54, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r2_hidden('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_51, c_16])).
% 1.98/1.18  tff(c_60, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_54])).
% 1.98/1.18  tff(c_61, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_60])).
% 1.98/1.18  tff(c_64, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_61])).
% 1.98/1.18  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_64])).
% 1.98/1.18  tff(c_69, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_60])).
% 1.98/1.18  tff(c_71, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_69])).
% 1.98/1.18  tff(c_74, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~r2_hidden('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_71])).
% 1.98/1.18  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_20, c_74])).
% 1.98/1.18  tff(c_79, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_69])).
% 1.98/1.18  tff(c_83, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_79])).
% 1.98/1.18  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_83])).
% 1.98/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.18  
% 1.98/1.18  Inference rules
% 1.98/1.18  ----------------------
% 1.98/1.18  #Ref     : 0
% 1.98/1.18  #Sup     : 10
% 1.98/1.18  #Fact    : 0
% 1.98/1.18  #Define  : 0
% 1.98/1.18  #Split   : 2
% 1.98/1.18  #Chain   : 0
% 1.98/1.18  #Close   : 0
% 1.98/1.18  
% 1.98/1.18  Ordering : KBO
% 1.98/1.18  
% 1.98/1.18  Simplification rules
% 1.98/1.18  ----------------------
% 1.98/1.18  #Subsume      : 0
% 1.98/1.18  #Demod        : 10
% 1.98/1.18  #Tautology    : 4
% 1.98/1.18  #SimpNegUnit  : 0
% 1.98/1.18  #BackRed      : 0
% 1.98/1.18  
% 1.98/1.18  #Partial instantiations: 0
% 1.98/1.18  #Strategies tried      : 1
% 1.98/1.18  
% 1.98/1.18  Timing (in seconds)
% 1.98/1.18  ----------------------
% 1.98/1.19  Preprocessing        : 0.28
% 1.98/1.19  Parsing              : 0.16
% 1.98/1.19  CNF conversion       : 0.02
% 1.98/1.19  Main loop            : 0.14
% 1.98/1.19  Inferencing          : 0.06
% 1.98/1.19  Reduction            : 0.04
% 1.98/1.19  Demodulation         : 0.03
% 1.98/1.19  BG Simplification    : 0.01
% 1.98/1.19  Subsumption          : 0.03
% 1.98/1.19  Abstraction          : 0.01
% 1.98/1.19  MUC search           : 0.00
% 1.98/1.19  Cooper               : 0.00
% 1.98/1.19  Total                : 0.46
% 1.98/1.19  Index Insertion      : 0.00
% 1.98/1.19  Index Deletion       : 0.00
% 1.98/1.19  Index Matching       : 0.00
% 1.98/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
