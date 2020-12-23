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
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  90 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_621,plain,(
    ! [C_71,A_72,B_73] :
      ( r1_tarski(k9_relat_1(C_71,k3_xboole_0(A_72,B_73)),k3_xboole_0(k9_relat_1(C_71,A_72),k9_relat_1(C_71,B_73)))
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_655,plain,(
    ! [C_74,A_75,B_76] :
      ( r1_tarski(k9_relat_1(C_74,k3_xboole_0(A_75,B_76)),k9_relat_1(C_74,A_75))
      | ~ v1_relat_1(C_74) ) ),
    inference(resolution,[status(thm)],[c_621,c_4])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_419,plain,(
    ! [C_50,A_51,B_52] :
      ( r1_tarski(k9_relat_1(C_50,k3_xboole_0(A_51,B_52)),k3_xboole_0(k9_relat_1(C_50,A_51),k9_relat_1(C_50,B_52)))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,B_19)
      | ~ r1_tarski(A_18,k3_xboole_0(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_18,B_2,A_1] :
      ( r1_tarski(A_18,B_2)
      | ~ r1_tarski(A_18,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_53])).

tff(c_454,plain,(
    ! [C_50,A_51,B_52] :
      ( r1_tarski(k9_relat_1(C_50,k3_xboole_0(A_51,B_52)),k9_relat_1(C_50,B_52))
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_419,c_59])).

tff(c_241,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,k9_relat_1(B_38,k1_relat_1(B_38))) = k9_relat_1(B_38,k10_relat_1(B_38,A_37))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_507,plain,(
    ! [A_62,A_63,B_64] :
      ( r1_tarski(A_62,A_63)
      | ~ r1_tarski(A_62,k9_relat_1(B_64,k10_relat_1(B_64,A_63)))
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_4])).

tff(c_572,plain,(
    ! [C_68,A_69,A_70] :
      ( r1_tarski(k9_relat_1(C_68,k3_xboole_0(A_69,k10_relat_1(C_68,A_70))),A_70)
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68) ) ),
    inference(resolution,[status(thm)],[c_454,c_507])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k3_xboole_0(B_7,C_8))
      | ~ r1_tarski(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_118,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_19])).

tff(c_350,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_593,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_572,c_350])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_593])).

tff(c_619,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_658,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_655,c_619])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.41  
% 2.57/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.41  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.41  
% 2.57/1.41  %Foreground sorts:
% 2.57/1.41  
% 2.57/1.41  
% 2.57/1.41  %Background operators:
% 2.57/1.41  
% 2.57/1.41  
% 2.57/1.41  %Foreground operators:
% 2.57/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.57/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.57/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.41  
% 2.57/1.42  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 2.57/1.42  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 2.57/1.42  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.57/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.57/1.42  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 2.57/1.42  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.57/1.42  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.42  tff(c_621, plain, (![C_71, A_72, B_73]: (r1_tarski(k9_relat_1(C_71, k3_xboole_0(A_72, B_73)), k3_xboole_0(k9_relat_1(C_71, A_72), k9_relat_1(C_71, B_73))) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.42  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.42  tff(c_655, plain, (![C_74, A_75, B_76]: (r1_tarski(k9_relat_1(C_74, k3_xboole_0(A_75, B_76)), k9_relat_1(C_74, A_75)) | ~v1_relat_1(C_74))), inference(resolution, [status(thm)], [c_621, c_4])).
% 2.57/1.42  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.42  tff(c_419, plain, (![C_50, A_51, B_52]: (r1_tarski(k9_relat_1(C_50, k3_xboole_0(A_51, B_52)), k3_xboole_0(k9_relat_1(C_50, A_51), k9_relat_1(C_50, B_52))) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.42  tff(c_53, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, B_19) | ~r1_tarski(A_18, k3_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.42  tff(c_59, plain, (![A_18, B_2, A_1]: (r1_tarski(A_18, B_2) | ~r1_tarski(A_18, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_53])).
% 2.57/1.42  tff(c_454, plain, (![C_50, A_51, B_52]: (r1_tarski(k9_relat_1(C_50, k3_xboole_0(A_51, B_52)), k9_relat_1(C_50, B_52)) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_419, c_59])).
% 2.57/1.42  tff(c_241, plain, (![A_37, B_38]: (k3_xboole_0(A_37, k9_relat_1(B_38, k1_relat_1(B_38)))=k9_relat_1(B_38, k10_relat_1(B_38, A_37)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.42  tff(c_507, plain, (![A_62, A_63, B_64]: (r1_tarski(A_62, A_63) | ~r1_tarski(A_62, k9_relat_1(B_64, k10_relat_1(B_64, A_63))) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_241, c_4])).
% 2.57/1.42  tff(c_572, plain, (![C_68, A_69, A_70]: (r1_tarski(k9_relat_1(C_68, k3_xboole_0(A_69, k10_relat_1(C_68, A_70))), A_70) | ~v1_funct_1(C_68) | ~v1_relat_1(C_68))), inference(resolution, [status(thm)], [c_454, c_507])).
% 2.57/1.42  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k3_xboole_0(B_7, C_8)) | ~r1_tarski(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.42  tff(c_14, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.42  tff(c_19, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.57/1.42  tff(c_118, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_19])).
% 2.57/1.42  tff(c_350, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_118])).
% 2.57/1.42  tff(c_593, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_572, c_350])).
% 2.57/1.42  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_593])).
% 2.57/1.42  tff(c_619, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_118])).
% 2.57/1.42  tff(c_658, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_655, c_619])).
% 2.57/1.42  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_658])).
% 2.57/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.42  
% 2.57/1.42  Inference rules
% 2.57/1.42  ----------------------
% 2.57/1.42  #Ref     : 0
% 2.57/1.42  #Sup     : 176
% 2.57/1.42  #Fact    : 0
% 2.57/1.42  #Define  : 0
% 2.57/1.42  #Split   : 1
% 2.57/1.42  #Chain   : 0
% 2.57/1.42  #Close   : 0
% 2.57/1.42  
% 2.57/1.42  Ordering : KBO
% 2.57/1.42  
% 2.57/1.42  Simplification rules
% 2.57/1.42  ----------------------
% 2.57/1.42  #Subsume      : 27
% 2.57/1.42  #Demod        : 28
% 2.57/1.42  #Tautology    : 42
% 2.57/1.42  #SimpNegUnit  : 0
% 2.57/1.42  #BackRed      : 0
% 2.57/1.42  
% 2.57/1.42  #Partial instantiations: 0
% 2.57/1.42  #Strategies tried      : 1
% 2.57/1.42  
% 2.57/1.42  Timing (in seconds)
% 2.57/1.42  ----------------------
% 2.57/1.42  Preprocessing        : 0.27
% 2.57/1.42  Parsing              : 0.15
% 2.57/1.43  CNF conversion       : 0.02
% 2.57/1.43  Main loop            : 0.37
% 2.57/1.43  Inferencing          : 0.13
% 2.57/1.43  Reduction            : 0.13
% 2.57/1.43  Demodulation         : 0.11
% 2.57/1.43  BG Simplification    : 0.02
% 2.57/1.43  Subsumption          : 0.07
% 2.57/1.43  Abstraction          : 0.02
% 2.57/1.43  MUC search           : 0.00
% 2.57/1.43  Cooper               : 0.00
% 2.57/1.43  Total                : 0.67
% 2.57/1.43  Index Insertion      : 0.00
% 2.57/1.43  Index Deletion       : 0.00
% 2.57/1.43  Index Matching       : 0.00
% 2.57/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
