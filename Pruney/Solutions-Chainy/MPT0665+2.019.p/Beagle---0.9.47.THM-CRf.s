%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 108 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 302 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_funct_1(k7_relat_1(A_6,B_7))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_hidden(A_3,k1_relat_1(k7_relat_1(C_5,B_4)))
      | ~ r2_hidden(A_3,k1_relat_1(C_5))
      | ~ r2_hidden(A_3,B_4)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [C_28,B_29,A_30] :
      ( k1_funct_1(k7_relat_1(C_28,B_29),A_30) = k1_funct_1(C_28,A_30)
      | ~ r2_hidden(A_30,k1_relat_1(k7_relat_1(C_28,B_29)))
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [C_31,B_32,A_33] :
      ( k1_funct_1(k7_relat_1(C_31,B_32),A_33) = k1_funct_1(C_31,A_33)
      | ~ v1_funct_1(C_31)
      | ~ r2_hidden(A_33,k1_relat_1(C_31))
      | ~ r2_hidden(A_33,B_32)
      | ~ v1_relat_1(C_31) ) ),
    inference(resolution,[status(thm)],[c_4,c_41])).

tff(c_50,plain,(
    ! [B_32] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_32),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden('#skF_1',B_32)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_55,plain,(
    ! [B_34] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_34),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ r2_hidden('#skF_1',B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_50])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(k1_funct_1(B_9,A_8),k2_relat_1(B_9))
      | ~ r2_hidden(A_8,k1_relat_1(B_9))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    ! [B_35] :
      ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),k2_relat_1(k7_relat_1('#skF_3',B_35)))
      | ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3',B_35)))
      | ~ v1_funct_1(k7_relat_1('#skF_3',B_35))
      | ~ v1_relat_1(k7_relat_1('#skF_3',B_35))
      | ~ r2_hidden('#skF_1',B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_14])).

tff(c_18,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),k2_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_18])).

tff(c_73,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_70])).

tff(c_86,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_89,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89])).

tff(c_94,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_96,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_99,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_22,c_99])).

tff(c_104,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_108,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.99/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.23  
% 1.99/1.24  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 1.99/1.24  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 1.99/1.24  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 1.99/1.24  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.99/1.24  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 1.99/1.24  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.99/1.24  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.24  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.24  tff(c_10, plain, (![A_6, B_7]: (v1_funct_1(k7_relat_1(A_6, B_7)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.24  tff(c_20, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.24  tff(c_22, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.24  tff(c_4, plain, (![A_3, C_5, B_4]: (r2_hidden(A_3, k1_relat_1(k7_relat_1(C_5, B_4))) | ~r2_hidden(A_3, k1_relat_1(C_5)) | ~r2_hidden(A_3, B_4) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.24  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.24  tff(c_41, plain, (![C_28, B_29, A_30]: (k1_funct_1(k7_relat_1(C_28, B_29), A_30)=k1_funct_1(C_28, A_30) | ~r2_hidden(A_30, k1_relat_1(k7_relat_1(C_28, B_29))) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.99/1.24  tff(c_46, plain, (![C_31, B_32, A_33]: (k1_funct_1(k7_relat_1(C_31, B_32), A_33)=k1_funct_1(C_31, A_33) | ~v1_funct_1(C_31) | ~r2_hidden(A_33, k1_relat_1(C_31)) | ~r2_hidden(A_33, B_32) | ~v1_relat_1(C_31))), inference(resolution, [status(thm)], [c_4, c_41])).
% 1.99/1.24  tff(c_50, plain, (![B_32]: (k1_funct_1(k7_relat_1('#skF_3', B_32), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~r2_hidden('#skF_1', B_32) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_46])).
% 1.99/1.24  tff(c_55, plain, (![B_34]: (k1_funct_1(k7_relat_1('#skF_3', B_34), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', B_34))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_50])).
% 1.99/1.24  tff(c_14, plain, (![B_9, A_8]: (r2_hidden(k1_funct_1(B_9, A_8), k2_relat_1(B_9)) | ~r2_hidden(A_8, k1_relat_1(B_9)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.24  tff(c_67, plain, (![B_35]: (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k2_relat_1(k7_relat_1('#skF_3', B_35))) | ~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', B_35))) | ~v1_funct_1(k7_relat_1('#skF_3', B_35)) | ~v1_relat_1(k7_relat_1('#skF_3', B_35)) | ~r2_hidden('#skF_1', B_35))), inference(superposition, [status(thm), theory('equality')], [c_55, c_14])).
% 1.99/1.24  tff(c_18, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k2_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.24  tff(c_70, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_67, c_18])).
% 1.99/1.24  tff(c_73, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_70])).
% 1.99/1.24  tff(c_86, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_73])).
% 1.99/1.24  tff(c_89, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_86])).
% 1.99/1.24  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_89])).
% 1.99/1.24  tff(c_94, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_73])).
% 1.99/1.24  tff(c_96, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_94])).
% 1.99/1.24  tff(c_99, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~r2_hidden('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_96])).
% 1.99/1.24  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_22, c_99])).
% 1.99/1.24  tff(c_104, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_94])).
% 1.99/1.24  tff(c_108, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_104])).
% 1.99/1.24  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_108])).
% 1.99/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  Inference rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Ref     : 0
% 1.99/1.24  #Sup     : 15
% 1.99/1.24  #Fact    : 0
% 1.99/1.24  #Define  : 0
% 1.99/1.24  #Split   : 2
% 1.99/1.24  #Chain   : 0
% 1.99/1.24  #Close   : 0
% 1.99/1.24  
% 1.99/1.24  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 1
% 1.99/1.25  #Demod        : 9
% 1.99/1.25  #Tautology    : 6
% 1.99/1.25  #SimpNegUnit  : 0
% 1.99/1.25  #BackRed      : 0
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.25  Preprocessing        : 0.29
% 1.99/1.25  Parsing              : 0.17
% 1.99/1.25  CNF conversion       : 0.02
% 1.99/1.25  Main loop            : 0.17
% 1.99/1.25  Inferencing          : 0.07
% 1.99/1.25  Reduction            : 0.04
% 1.99/1.25  Demodulation         : 0.03
% 1.99/1.25  BG Simplification    : 0.01
% 1.99/1.25  Subsumption          : 0.03
% 1.99/1.25  Abstraction          : 0.01
% 1.99/1.25  MUC search           : 0.00
% 1.99/1.25  Cooper               : 0.00
% 1.99/1.25  Total                : 0.49
% 1.99/1.25  Index Insertion      : 0.00
% 1.99/1.25  Index Deletion       : 0.00
% 1.99/1.25  Index Matching       : 0.00
% 1.99/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
