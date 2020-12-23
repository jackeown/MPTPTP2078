%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 130 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v2_funct_1(A)
              & r1_tarski(B,k1_relat_1(A)) )
           => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [B_15,A_16] :
      ( k10_relat_1(B_15,k9_relat_1(B_15,A_16)) = A_16
      | ~ v2_funct_1(B_15)
      | ~ r1_tarski(A_16,k1_relat_1(B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_73,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_70])).

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

tff(c_6,plain,(
    ! [A_2] :
      ( v2_funct_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [B_13,A_14] :
      ( k10_relat_1(k2_funct_1(B_13),A_14) = k9_relat_1(B_13,A_14)
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [A_17,A_18] :
      ( k9_relat_1(k2_funct_1(A_17),A_18) = k10_relat_1(A_17,A_18)
      | ~ v2_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(k2_funct_1(A_17))
      | ~ v1_relat_1(k2_funct_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_84,plain,(
    ! [A_19,A_20] :
      ( k9_relat_1(k2_funct_1(A_19),A_20) = k10_relat_1(A_19,A_20)
      | ~ v1_funct_1(k2_funct_1(A_19))
      | ~ v1_relat_1(k2_funct_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_90,plain,(
    ! [A_21,A_22] :
      ( k9_relat_1(k2_funct_1(A_21),A_22) = k10_relat_1(A_21,A_22)
      | ~ v1_funct_1(k2_funct_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_96,plain,(
    ! [A_23,A_24] :
      ( k9_relat_1(k2_funct_1(A_23),A_24) = k10_relat_1(A_23,A_24)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_18,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_102,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_18])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_73,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n008.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:53:45 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.70/1.14  
% 1.70/1.14  %Foreground sorts:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Background operators:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Foreground operators:
% 1.70/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.70/1.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.70/1.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.70/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.70/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.14  
% 1.70/1.15  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 1.70/1.15  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 1.70/1.15  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.70/1.15  tff(f_45, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 1.70/1.15  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 1.70/1.15  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 1.70/1.15  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.70/1.15  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.70/1.15  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.70/1.15  tff(c_20, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.70/1.15  tff(c_68, plain, (![B_15, A_16]: (k10_relat_1(B_15, k9_relat_1(B_15, A_16))=A_16 | ~v2_funct_1(B_15) | ~r1_tarski(A_16, k1_relat_1(B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.15  tff(c_70, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.70/1.15  tff(c_73, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_70])).
% 1.70/1.15  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.15  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.15  tff(c_6, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.15  tff(c_16, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.70/1.15  tff(c_56, plain, (![B_13, A_14]: (k10_relat_1(k2_funct_1(B_13), A_14)=k9_relat_1(B_13, A_14) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.70/1.15  tff(c_78, plain, (![A_17, A_18]: (k9_relat_1(k2_funct_1(A_17), A_18)=k10_relat_1(A_17, A_18) | ~v2_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(k2_funct_1(A_17)) | ~v1_relat_1(k2_funct_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_16, c_56])).
% 1.70/1.15  tff(c_84, plain, (![A_19, A_20]: (k9_relat_1(k2_funct_1(A_19), A_20)=k10_relat_1(A_19, A_20) | ~v1_funct_1(k2_funct_1(A_19)) | ~v1_relat_1(k2_funct_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_6, c_78])).
% 1.70/1.15  tff(c_90, plain, (![A_21, A_22]: (k9_relat_1(k2_funct_1(A_21), A_22)=k10_relat_1(A_21, A_22) | ~v1_funct_1(k2_funct_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(resolution, [status(thm)], [c_4, c_84])).
% 1.70/1.15  tff(c_96, plain, (![A_23, A_24]: (k9_relat_1(k2_funct_1(A_23), A_24)=k10_relat_1(A_23, A_24) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(resolution, [status(thm)], [c_2, c_90])).
% 1.70/1.15  tff(c_18, plain, (k9_relat_1(k2_funct_1('#skF_1'), k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.70/1.15  tff(c_102, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_18])).
% 1.70/1.15  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_73, c_102])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 23
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 0
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 6
% 1.70/1.15  #Demod        : 7
% 1.70/1.15  #Tautology    : 12
% 1.70/1.15  #SimpNegUnit  : 0
% 1.70/1.15  #BackRed      : 0
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.15  Timing (in seconds)
% 1.70/1.15  ----------------------
% 1.70/1.16  Preprocessing        : 0.27
% 1.70/1.16  Parsing              : 0.15
% 1.70/1.16  CNF conversion       : 0.02
% 1.70/1.16  Main loop            : 0.14
% 1.70/1.16  Inferencing          : 0.06
% 1.70/1.16  Reduction            : 0.04
% 1.70/1.16  Demodulation         : 0.03
% 1.70/1.16  BG Simplification    : 0.01
% 1.70/1.16  Subsumption          : 0.03
% 1.70/1.16  Abstraction          : 0.01
% 1.70/1.16  MUC search           : 0.00
% 1.70/1.16  Cooper               : 0.00
% 1.70/1.16  Total                : 0.45
% 1.70/1.16  Index Insertion      : 0.00
% 1.70/1.16  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
