%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 125 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 282 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
        <=> ! [B] :
            ? [C] : r1_tarski(k10_relat_1(A,k1_tarski(B)),k1_tarski(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [C_35] :
      ( ~ r1_tarski(k10_relat_1('#skF_3',k1_tarski('#skF_4')),k1_tarski(C_35))
      | ~ v2_funct_1('#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_101,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,(
    ! [B_36] :
      ( v2_funct_1('#skF_3')
      | r1_tarski(k10_relat_1('#skF_3',k1_tarski(B_36)),k1_tarski('#skF_5'(B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_190,plain,(
    ! [B_59] : r1_tarski(k10_relat_1('#skF_3',k1_tarski(B_59)),k1_tarski('#skF_5'(B_59))) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_42])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k1_tarski(B_14) = A_13
      | k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_414,plain,(
    ! [B_89] :
      ( k10_relat_1('#skF_3',k1_tarski(B_89)) = k1_tarski('#skF_5'(B_89))
      | k10_relat_1('#skF_3',k1_tarski(B_89)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_190,c_16])).

tff(c_28,plain,(
    ! [C_25,A_17] :
      ( k1_tarski(C_25) != k10_relat_1(A_17,k1_tarski('#skF_1'(A_17)))
      | v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_427,plain,(
    ! [C_25] :
      ( k1_tarski(C_25) != k1_tarski('#skF_5'('#skF_1'('#skF_3')))
      | v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_28])).

tff(c_437,plain,(
    ! [C_25] :
      ( k1_tarski(C_25) != k1_tarski('#skF_5'('#skF_1'('#skF_3')))
      | v2_funct_1('#skF_3')
      | k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_427])).

tff(c_438,plain,(
    ! [C_25] :
      ( k1_tarski(C_25) != k1_tarski('#skF_5'('#skF_1'('#skF_3')))
      | k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_437])).

tff(c_551,plain,(
    ! [C_25] : k1_tarski(C_25) != k1_tarski('#skF_5'('#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_555,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_551])).

tff(c_556,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_30,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_1'(A_17),k2_relat_1(A_17))
      | v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_280,plain,(
    ! [B_71,A_72] :
      ( k10_relat_1(B_71,k1_tarski(A_72)) != k1_xboole_0
      | ~ r2_hidden(A_72,k2_relat_1(B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_284,plain,(
    ! [A_17] :
      ( k10_relat_1(A_17,k1_tarski('#skF_1'(A_17))) != k1_xboole_0
      | v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_30,c_280])).

tff(c_572,plain,
    ( v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_284])).

tff(c_603,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_572])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_603])).

tff(c_607,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,k2_relat_1(B_16))
      | k10_relat_1(B_16,k1_tarski(A_15)) = k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_978,plain,(
    ! [A_152,B_153] :
      ( k10_relat_1(A_152,k1_tarski(B_153)) = k1_tarski('#skF_2'(A_152,B_153))
      | ~ r2_hidden(B_153,k2_relat_1(A_152))
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1508,plain,(
    ! [B_178,A_179] :
      ( k10_relat_1(B_178,k1_tarski(A_179)) = k1_tarski('#skF_2'(B_178,A_179))
      | ~ v2_funct_1(B_178)
      | ~ v1_funct_1(B_178)
      | k10_relat_1(B_178,k1_tarski(A_179)) = k1_xboole_0
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_22,c_978])).

tff(c_606,plain,(
    ! [C_35] : ~ r1_tarski(k10_relat_1('#skF_3',k1_tarski('#skF_4')),k1_tarski(C_35)) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1522,plain,(
    ! [C_35] :
      ( ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_tarski(C_35))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | k10_relat_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_606])).

tff(c_1528,plain,(
    ! [C_35] :
      ( ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_tarski(C_35))
      | k10_relat_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_607,c_1522])).

tff(c_1531,plain,(
    ! [C_180] : ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_tarski(C_180)) ),
    inference(splitLeft,[status(thm)],[c_1528])).

tff(c_1536,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1531])).

tff(c_1537,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1528])).

tff(c_1538,plain,(
    ! [C_35] : ~ r1_tarski(k1_xboole_0,k1_tarski(C_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_606])).

tff(c_1541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.13/1.48  
% 3.13/1.48  %Foreground sorts:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Background operators:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Foreground operators:
% 3.13/1.48  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.13/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.13/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.13/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.48  
% 3.19/1.49  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.19/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.49  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: (?[C]: r1_tarski(k10_relat_1(A, k1_tarski(B)), k1_tarski(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_1)).
% 3.19/1.49  tff(f_56, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.19/1.49  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B]: ~(r2_hidden(B, k2_relat_1(A)) & (![C]: ~(k10_relat_1(A, k1_tarski(B)) = k1_tarski(C))))) <=> v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_funct_1)).
% 3.19/1.49  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 3.19/1.49  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.49  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.49  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.49  tff(c_36, plain, (![C_35]: (~r1_tarski(k10_relat_1('#skF_3', k1_tarski('#skF_4')), k1_tarski(C_35)) | ~v2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.49  tff(c_101, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 3.19/1.49  tff(c_42, plain, (![B_36]: (v2_funct_1('#skF_3') | r1_tarski(k10_relat_1('#skF_3', k1_tarski(B_36)), k1_tarski('#skF_5'(B_36))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.49  tff(c_190, plain, (![B_59]: (r1_tarski(k10_relat_1('#skF_3', k1_tarski(B_59)), k1_tarski('#skF_5'(B_59))))), inference(negUnitSimplification, [status(thm)], [c_101, c_42])).
% 3.19/1.49  tff(c_16, plain, (![B_14, A_13]: (k1_tarski(B_14)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.19/1.49  tff(c_414, plain, (![B_89]: (k10_relat_1('#skF_3', k1_tarski(B_89))=k1_tarski('#skF_5'(B_89)) | k10_relat_1('#skF_3', k1_tarski(B_89))=k1_xboole_0)), inference(resolution, [status(thm)], [c_190, c_16])).
% 3.19/1.49  tff(c_28, plain, (![C_25, A_17]: (k1_tarski(C_25)!=k10_relat_1(A_17, k1_tarski('#skF_1'(A_17))) | v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.19/1.49  tff(c_427, plain, (![C_25]: (k1_tarski(C_25)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))) | v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_414, c_28])).
% 3.19/1.49  tff(c_437, plain, (![C_25]: (k1_tarski(C_25)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))) | v2_funct_1('#skF_3') | k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_427])).
% 3.19/1.49  tff(c_438, plain, (![C_25]: (k1_tarski(C_25)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))) | k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_101, c_437])).
% 3.19/1.49  tff(c_551, plain, (![C_25]: (k1_tarski(C_25)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))))), inference(splitLeft, [status(thm)], [c_438])).
% 3.19/1.49  tff(c_555, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_551])).
% 3.19/1.49  tff(c_556, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_438])).
% 3.19/1.49  tff(c_30, plain, (![A_17]: (r2_hidden('#skF_1'(A_17), k2_relat_1(A_17)) | v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.19/1.49  tff(c_280, plain, (![B_71, A_72]: (k10_relat_1(B_71, k1_tarski(A_72))!=k1_xboole_0 | ~r2_hidden(A_72, k2_relat_1(B_71)) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.19/1.49  tff(c_284, plain, (![A_17]: (k10_relat_1(A_17, k1_tarski('#skF_1'(A_17)))!=k1_xboole_0 | v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_30, c_280])).
% 3.19/1.49  tff(c_572, plain, (v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_556, c_284])).
% 3.19/1.49  tff(c_603, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_572])).
% 3.19/1.49  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_603])).
% 3.19/1.49  tff(c_607, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.19/1.49  tff(c_22, plain, (![A_15, B_16]: (r2_hidden(A_15, k2_relat_1(B_16)) | k10_relat_1(B_16, k1_tarski(A_15))=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.19/1.49  tff(c_978, plain, (![A_152, B_153]: (k10_relat_1(A_152, k1_tarski(B_153))=k1_tarski('#skF_2'(A_152, B_153)) | ~r2_hidden(B_153, k2_relat_1(A_152)) | ~v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.19/1.49  tff(c_1508, plain, (![B_178, A_179]: (k10_relat_1(B_178, k1_tarski(A_179))=k1_tarski('#skF_2'(B_178, A_179)) | ~v2_funct_1(B_178) | ~v1_funct_1(B_178) | k10_relat_1(B_178, k1_tarski(A_179))=k1_xboole_0 | ~v1_relat_1(B_178))), inference(resolution, [status(thm)], [c_22, c_978])).
% 3.19/1.49  tff(c_606, plain, (![C_35]: (~r1_tarski(k10_relat_1('#skF_3', k1_tarski('#skF_4')), k1_tarski(C_35)))), inference(splitRight, [status(thm)], [c_36])).
% 3.19/1.49  tff(c_1522, plain, (![C_35]: (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_tarski(C_35)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | k10_relat_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1508, c_606])).
% 3.19/1.49  tff(c_1528, plain, (![C_35]: (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_tarski(C_35)) | k10_relat_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_607, c_1522])).
% 3.19/1.49  tff(c_1531, plain, (![C_180]: (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_tarski(C_180)))), inference(splitLeft, [status(thm)], [c_1528])).
% 3.19/1.49  tff(c_1536, plain, $false, inference(resolution, [status(thm)], [c_6, c_1531])).
% 3.19/1.49  tff(c_1537, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1528])).
% 3.19/1.49  tff(c_1538, plain, (![C_35]: (~r1_tarski(k1_xboole_0, k1_tarski(C_35)))), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_606])).
% 3.19/1.49  tff(c_1541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1538])).
% 3.19/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  Inference rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Ref     : 1
% 3.19/1.49  #Sup     : 334
% 3.19/1.49  #Fact    : 5
% 3.19/1.49  #Define  : 0
% 3.19/1.49  #Split   : 4
% 3.19/1.49  #Chain   : 0
% 3.19/1.49  #Close   : 0
% 3.19/1.49  
% 3.19/1.49  Ordering : KBO
% 3.19/1.49  
% 3.19/1.49  Simplification rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Subsume      : 64
% 3.19/1.49  #Demod        : 313
% 3.19/1.49  #Tautology    : 172
% 3.19/1.49  #SimpNegUnit  : 7
% 3.19/1.49  #BackRed      : 1
% 3.19/1.49  
% 3.19/1.49  #Partial instantiations: 0
% 3.19/1.49  #Strategies tried      : 1
% 3.19/1.49  
% 3.19/1.49  Timing (in seconds)
% 3.19/1.49  ----------------------
% 3.19/1.49  Preprocessing        : 0.30
% 3.19/1.49  Parsing              : 0.16
% 3.19/1.49  CNF conversion       : 0.02
% 3.19/1.49  Main loop            : 0.43
% 3.19/1.49  Inferencing          : 0.16
% 3.19/1.49  Reduction            : 0.14
% 3.19/1.49  Demodulation         : 0.10
% 3.19/1.49  BG Simplification    : 0.02
% 3.19/1.50  Subsumption          : 0.08
% 3.19/1.50  Abstraction          : 0.03
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.76
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
