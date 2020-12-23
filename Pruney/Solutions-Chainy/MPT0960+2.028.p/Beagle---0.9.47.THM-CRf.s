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
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 100 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_36,plain,(
    ! [A_33] : v1_relat_1(k1_wellord2(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_25] :
      ( k3_relat_1(k1_wellord2(A_25)) = A_25
      | ~ v1_relat_1(k1_wellord2(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_25] : k3_relat_1(k1_wellord2(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_104,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(k4_tarski('#skF_1'(A_58,B_59),'#skF_2'(A_58,B_59)),A_58)
      | r1_tarski(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_22,C_24,B_23] :
      ( r2_hidden(A_22,k3_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_144,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),k3_relat_1(A_68))
      | r1_tarski(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_147,plain,(
    ! [A_25,B_69] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_25),B_69),A_25)
      | r1_tarski(k1_wellord2(A_25),B_69)
      | ~ v1_relat_1(k1_wellord2(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_144])).

tff(c_149,plain,(
    ! [A_25,B_69] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_25),B_69),A_25)
      | r1_tarski(k1_wellord2(A_25),B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_147])).

tff(c_14,plain,(
    ! [B_23,C_24,A_22] :
      ( r2_hidden(B_23,k3_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),k3_relat_1(A_61))
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_104,c_14])).

tff(c_132,plain,(
    ! [A_25,B_62] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_25),B_62),A_25)
      | r1_tarski(k1_wellord2(A_25),B_62)
      | ~ v1_relat_1(k1_wellord2(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_129])).

tff(c_134,plain,(
    ! [A_25,B_62] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_25),B_62),A_25)
      | r1_tarski(k1_wellord2(A_25),B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_132])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_56,B_57),'#skF_2'(A_56,B_57)),B_57)
      | r1_tarski(A_56,B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_729,plain,(
    ! [A_151,C_152,D_153] :
      ( r1_tarski(A_151,k2_zfmisc_1(C_152,D_153))
      | ~ v1_relat_1(A_151)
      | ~ r2_hidden('#skF_2'(A_151,k2_zfmisc_1(C_152,D_153)),D_153)
      | ~ r2_hidden('#skF_1'(A_151,k2_zfmisc_1(C_152,D_153)),C_152) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_759,plain,(
    ! [A_25,C_152] :
      ( ~ v1_relat_1(k1_wellord2(A_25))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_25),k2_zfmisc_1(C_152,A_25)),C_152)
      | r1_tarski(k1_wellord2(A_25),k2_zfmisc_1(C_152,A_25)) ) ),
    inference(resolution,[status(thm)],[c_134,c_729])).

tff(c_776,plain,(
    ! [A_154,C_155] :
      ( ~ r2_hidden('#skF_1'(k1_wellord2(A_154),k2_zfmisc_1(C_155,A_154)),C_155)
      | r1_tarski(k1_wellord2(A_154),k2_zfmisc_1(C_155,A_154)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_759])).

tff(c_829,plain,(
    ! [A_25] : r1_tarski(k1_wellord2(A_25),k2_zfmisc_1(A_25,A_25)) ),
    inference(resolution,[status(thm)],[c_149,c_776])).

tff(c_38,plain,(
    ~ r1_tarski(k1_wellord2('#skF_5'),k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_38])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.46  
% 3.02/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.02/1.46  
% 3.02/1.46  %Foreground sorts:
% 3.02/1.46  
% 3.02/1.46  
% 3.02/1.46  %Background operators:
% 3.02/1.46  
% 3.02/1.46  
% 3.02/1.46  %Foreground operators:
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.02/1.46  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.02/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.02/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.46  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.02/1.46  
% 3.06/1.47  tff(f_66, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.06/1.47  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.06/1.47  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 3.06/1.47  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 3.06/1.47  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.06/1.47  tff(f_69, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 3.06/1.47  tff(c_36, plain, (![A_33]: (v1_relat_1(k1_wellord2(A_33)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.47  tff(c_30, plain, (![A_25]: (k3_relat_1(k1_wellord2(A_25))=A_25 | ~v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.47  tff(c_44, plain, (![A_25]: (k3_relat_1(k1_wellord2(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30])).
% 3.06/1.47  tff(c_104, plain, (![A_58, B_59]: (r2_hidden(k4_tarski('#skF_1'(A_58, B_59), '#skF_2'(A_58, B_59)), A_58) | r1_tarski(A_58, B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.47  tff(c_16, plain, (![A_22, C_24, B_23]: (r2_hidden(A_22, k3_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.47  tff(c_144, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), k3_relat_1(A_68)) | r1_tarski(A_68, B_69) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_104, c_16])).
% 3.06/1.47  tff(c_147, plain, (![A_25, B_69]: (r2_hidden('#skF_1'(k1_wellord2(A_25), B_69), A_25) | r1_tarski(k1_wellord2(A_25), B_69) | ~v1_relat_1(k1_wellord2(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_144])).
% 3.06/1.47  tff(c_149, plain, (![A_25, B_69]: (r2_hidden('#skF_1'(k1_wellord2(A_25), B_69), A_25) | r1_tarski(k1_wellord2(A_25), B_69))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_147])).
% 3.06/1.47  tff(c_14, plain, (![B_23, C_24, A_22]: (r2_hidden(B_23, k3_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.47  tff(c_129, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), k3_relat_1(A_61)) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_104, c_14])).
% 3.06/1.47  tff(c_132, plain, (![A_25, B_62]: (r2_hidden('#skF_2'(k1_wellord2(A_25), B_62), A_25) | r1_tarski(k1_wellord2(A_25), B_62) | ~v1_relat_1(k1_wellord2(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_129])).
% 3.06/1.47  tff(c_134, plain, (![A_25, B_62]: (r2_hidden('#skF_2'(k1_wellord2(A_25), B_62), A_25) | r1_tarski(k1_wellord2(A_25), B_62))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_132])).
% 3.06/1.47  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.47  tff(c_98, plain, (![A_56, B_57]: (~r2_hidden(k4_tarski('#skF_1'(A_56, B_57), '#skF_2'(A_56, B_57)), B_57) | r1_tarski(A_56, B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.47  tff(c_729, plain, (![A_151, C_152, D_153]: (r1_tarski(A_151, k2_zfmisc_1(C_152, D_153)) | ~v1_relat_1(A_151) | ~r2_hidden('#skF_2'(A_151, k2_zfmisc_1(C_152, D_153)), D_153) | ~r2_hidden('#skF_1'(A_151, k2_zfmisc_1(C_152, D_153)), C_152))), inference(resolution, [status(thm)], [c_2, c_98])).
% 3.06/1.47  tff(c_759, plain, (![A_25, C_152]: (~v1_relat_1(k1_wellord2(A_25)) | ~r2_hidden('#skF_1'(k1_wellord2(A_25), k2_zfmisc_1(C_152, A_25)), C_152) | r1_tarski(k1_wellord2(A_25), k2_zfmisc_1(C_152, A_25)))), inference(resolution, [status(thm)], [c_134, c_729])).
% 3.06/1.47  tff(c_776, plain, (![A_154, C_155]: (~r2_hidden('#skF_1'(k1_wellord2(A_154), k2_zfmisc_1(C_155, A_154)), C_155) | r1_tarski(k1_wellord2(A_154), k2_zfmisc_1(C_155, A_154)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_759])).
% 3.06/1.47  tff(c_829, plain, (![A_25]: (r1_tarski(k1_wellord2(A_25), k2_zfmisc_1(A_25, A_25)))), inference(resolution, [status(thm)], [c_149, c_776])).
% 3.06/1.47  tff(c_38, plain, (~r1_tarski(k1_wellord2('#skF_5'), k2_zfmisc_1('#skF_5', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.06/1.47  tff(c_835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_829, c_38])).
% 3.06/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  Inference rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Ref     : 0
% 3.06/1.47  #Sup     : 173
% 3.06/1.47  #Fact    : 0
% 3.06/1.47  #Define  : 0
% 3.06/1.47  #Split   : 0
% 3.06/1.47  #Chain   : 0
% 3.06/1.47  #Close   : 0
% 3.06/1.47  
% 3.06/1.47  Ordering : KBO
% 3.06/1.47  
% 3.06/1.47  Simplification rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Subsume      : 28
% 3.06/1.47  #Demod        : 80
% 3.06/1.47  #Tautology    : 21
% 3.06/1.47  #SimpNegUnit  : 0
% 3.06/1.47  #BackRed      : 1
% 3.06/1.47  
% 3.06/1.47  #Partial instantiations: 0
% 3.06/1.47  #Strategies tried      : 1
% 3.06/1.47  
% 3.06/1.47  Timing (in seconds)
% 3.06/1.47  ----------------------
% 3.06/1.48  Preprocessing        : 0.31
% 3.06/1.48  Parsing              : 0.16
% 3.06/1.48  CNF conversion       : 0.02
% 3.06/1.48  Main loop            : 0.38
% 3.06/1.48  Inferencing          : 0.15
% 3.06/1.48  Reduction            : 0.10
% 3.06/1.48  Demodulation         : 0.07
% 3.06/1.48  BG Simplification    : 0.03
% 3.06/1.48  Subsumption          : 0.09
% 3.06/1.48  Abstraction          : 0.02
% 3.06/1.48  MUC search           : 0.00
% 3.06/1.48  Cooper               : 0.00
% 3.06/1.48  Total                : 0.72
% 3.06/1.48  Index Insertion      : 0.00
% 3.06/1.48  Index Deletion       : 0.00
% 3.06/1.48  Index Matching       : 0.00
% 3.06/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
