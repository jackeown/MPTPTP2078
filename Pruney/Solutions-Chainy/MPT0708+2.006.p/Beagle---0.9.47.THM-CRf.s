%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:24 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 212 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(A,k1_relat_1(C))
            & r1_tarski(k9_relat_1(C,A),B) )
         => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_1'(A_22,B_23),B_23)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_32,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_45,plain,(
    ! [C_25,B_26,A_27] :
      ( r2_hidden(C_25,B_26)
      | ~ r2_hidden(C_25,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [A_31,B_32,B_33] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_33)
      | ~ r1_tarski(A_31,B_33)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_39,B_40,B_41,B_42] :
      ( r2_hidden('#skF_1'(A_39,B_40),B_41)
      | ~ r1_tarski(B_42,B_41)
      | ~ r1_tarski(A_39,B_42)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_92,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_43,'#skF_4')
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_99,plain,(
    ! [A_43,B_44,B_2] :
      ( r2_hidden('#skF_1'(A_43,B_44),B_2)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_2)
      | ~ r1_tarski(A_43,'#skF_4')
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,k10_relat_1(B_19,k9_relat_1(B_19,A_18)))
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_672,plain,(
    ! [A_139,B_140,B_141,A_142] :
      ( r2_hidden('#skF_1'(A_139,B_140),k10_relat_1(B_141,k9_relat_1(B_141,A_142)))
      | ~ r1_tarski(A_139,A_142)
      | r1_tarski(A_139,B_140)
      | ~ r1_tarski(A_142,k1_relat_1(B_141))
      | ~ v1_relat_1(B_141) ) ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_30,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,(
    ! [A_36,D_37,B_38] :
      ( r2_hidden(k1_funct_1(A_36,D_37),B_38)
      | ~ r2_hidden(D_37,k10_relat_1(A_36,B_38))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_215,plain,(
    ! [A_73,D_74,B_75,B_76] :
      ( r2_hidden(k1_funct_1(A_73,D_74),B_75)
      | ~ r1_tarski(B_76,B_75)
      | ~ r2_hidden(D_74,k10_relat_1(A_73,B_76))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_232,plain,(
    ! [A_73,D_74] :
      ( r2_hidden(k1_funct_1(A_73,D_74),'#skF_5')
      | ~ r2_hidden(D_74,k10_relat_1(A_73,k9_relat_1('#skF_6','#skF_4')))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_30,c_215])).

tff(c_678,plain,(
    ! [A_139,B_140] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_1'(A_139,B_140)),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r1_tarski(A_139,'#skF_4')
      | r1_tarski(A_139,B_140)
      | ~ r1_tarski('#skF_4',k1_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_672,c_232])).

tff(c_695,plain,(
    ! [A_143,B_144] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_1'(A_143,B_144)),'#skF_5')
      | ~ r1_tarski(A_143,'#skF_4')
      | r1_tarski(A_143,B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_34,c_678])).

tff(c_8,plain,(
    ! [D_17,A_6,B_13] :
      ( r2_hidden(D_17,k10_relat_1(A_6,B_13))
      | ~ r2_hidden(k1_funct_1(A_6,D_17),B_13)
      | ~ r2_hidden(D_17,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_698,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_1'(A_143,B_144),k10_relat_1('#skF_6','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_143,B_144),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski(A_143,'#skF_4')
      | r1_tarski(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_695,c_8])).

tff(c_891,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_1'(A_163,B_164),k10_relat_1('#skF_6','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_163,B_164),k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_163,'#skF_4')
      | r1_tarski(A_163,B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_698])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_911,plain,(
    ! [A_165] :
      ( ~ r2_hidden('#skF_1'(A_165,k10_relat_1('#skF_6','#skF_5')),k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_165,'#skF_4')
      | r1_tarski(A_165,k10_relat_1('#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_891,c_4])).

tff(c_927,plain,(
    ! [A_43] :
      ( ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_43,'#skF_4')
      | r1_tarski(A_43,k10_relat_1('#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_99,c_911])).

tff(c_951,plain,(
    ! [A_166] :
      ( ~ r1_tarski(A_166,'#skF_4')
      | r1_tarski(A_166,k10_relat_1('#skF_6','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_927])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_978,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_951,c_28])).

tff(c_996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.30  
% 5.09/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.30  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.09/2.30  
% 5.09/2.30  %Foreground sorts:
% 5.09/2.30  
% 5.09/2.30  
% 5.09/2.30  %Background operators:
% 5.09/2.30  
% 5.09/2.30  
% 5.09/2.30  %Foreground operators:
% 5.09/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.09/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/2.30  tff('#skF_5', type, '#skF_5': $i).
% 5.09/2.30  tff('#skF_6', type, '#skF_6': $i).
% 5.09/2.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.09/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.09/2.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.09/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/2.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.09/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.09/2.30  tff('#skF_4', type, '#skF_4': $i).
% 5.09/2.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.09/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.09/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.09/2.30  
% 5.09/2.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.09/2.32  tff(f_63, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 5.09/2.32  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.09/2.32  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 5.09/2.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/2.32  tff(c_38, plain, (![A_22, B_23]: (~r2_hidden('#skF_1'(A_22, B_23), B_23) | r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/2.32  tff(c_43, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_38])).
% 5.09/2.32  tff(c_32, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.09/2.32  tff(c_45, plain, (![C_25, B_26, A_27]: (r2_hidden(C_25, B_26) | ~r2_hidden(C_25, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/2.32  tff(c_55, plain, (![A_31, B_32, B_33]: (r2_hidden('#skF_1'(A_31, B_32), B_33) | ~r1_tarski(A_31, B_33) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_6, c_45])).
% 5.09/2.32  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/2.32  tff(c_79, plain, (![A_39, B_40, B_41, B_42]: (r2_hidden('#skF_1'(A_39, B_40), B_41) | ~r1_tarski(B_42, B_41) | ~r1_tarski(A_39, B_42) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_55, c_2])).
% 5.09/2.32  tff(c_92, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), k1_relat_1('#skF_6')) | ~r1_tarski(A_43, '#skF_4') | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_32, c_79])).
% 5.09/2.32  tff(c_99, plain, (![A_43, B_44, B_2]: (r2_hidden('#skF_1'(A_43, B_44), B_2) | ~r1_tarski(k1_relat_1('#skF_6'), B_2) | ~r1_tarski(A_43, '#skF_4') | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_92, c_2])).
% 5.09/2.32  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.09/2.32  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.09/2.32  tff(c_26, plain, (![A_18, B_19]: (r1_tarski(A_18, k10_relat_1(B_19, k9_relat_1(B_19, A_18))) | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.09/2.32  tff(c_672, plain, (![A_139, B_140, B_141, A_142]: (r2_hidden('#skF_1'(A_139, B_140), k10_relat_1(B_141, k9_relat_1(B_141, A_142))) | ~r1_tarski(A_139, A_142) | r1_tarski(A_139, B_140) | ~r1_tarski(A_142, k1_relat_1(B_141)) | ~v1_relat_1(B_141))), inference(resolution, [status(thm)], [c_26, c_79])).
% 5.09/2.32  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.09/2.32  tff(c_70, plain, (![A_36, D_37, B_38]: (r2_hidden(k1_funct_1(A_36, D_37), B_38) | ~r2_hidden(D_37, k10_relat_1(A_36, B_38)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.09/2.32  tff(c_215, plain, (![A_73, D_74, B_75, B_76]: (r2_hidden(k1_funct_1(A_73, D_74), B_75) | ~r1_tarski(B_76, B_75) | ~r2_hidden(D_74, k10_relat_1(A_73, B_76)) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_70, c_2])).
% 5.09/2.32  tff(c_232, plain, (![A_73, D_74]: (r2_hidden(k1_funct_1(A_73, D_74), '#skF_5') | ~r2_hidden(D_74, k10_relat_1(A_73, k9_relat_1('#skF_6', '#skF_4'))) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_30, c_215])).
% 5.09/2.32  tff(c_678, plain, (![A_139, B_140]: (r2_hidden(k1_funct_1('#skF_6', '#skF_1'(A_139, B_140)), '#skF_5') | ~v1_funct_1('#skF_6') | ~r1_tarski(A_139, '#skF_4') | r1_tarski(A_139, B_140) | ~r1_tarski('#skF_4', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_672, c_232])).
% 5.09/2.32  tff(c_695, plain, (![A_143, B_144]: (r2_hidden(k1_funct_1('#skF_6', '#skF_1'(A_143, B_144)), '#skF_5') | ~r1_tarski(A_143, '#skF_4') | r1_tarski(A_143, B_144))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_34, c_678])).
% 5.09/2.32  tff(c_8, plain, (![D_17, A_6, B_13]: (r2_hidden(D_17, k10_relat_1(A_6, B_13)) | ~r2_hidden(k1_funct_1(A_6, D_17), B_13) | ~r2_hidden(D_17, k1_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.09/2.32  tff(c_698, plain, (![A_143, B_144]: (r2_hidden('#skF_1'(A_143, B_144), k10_relat_1('#skF_6', '#skF_5')) | ~r2_hidden('#skF_1'(A_143, B_144), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r1_tarski(A_143, '#skF_4') | r1_tarski(A_143, B_144))), inference(resolution, [status(thm)], [c_695, c_8])).
% 5.09/2.32  tff(c_891, plain, (![A_163, B_164]: (r2_hidden('#skF_1'(A_163, B_164), k10_relat_1('#skF_6', '#skF_5')) | ~r2_hidden('#skF_1'(A_163, B_164), k1_relat_1('#skF_6')) | ~r1_tarski(A_163, '#skF_4') | r1_tarski(A_163, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_698])).
% 5.09/2.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/2.32  tff(c_911, plain, (![A_165]: (~r2_hidden('#skF_1'(A_165, k10_relat_1('#skF_6', '#skF_5')), k1_relat_1('#skF_6')) | ~r1_tarski(A_165, '#skF_4') | r1_tarski(A_165, k10_relat_1('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_891, c_4])).
% 5.09/2.32  tff(c_927, plain, (![A_43]: (~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_6')) | ~r1_tarski(A_43, '#skF_4') | r1_tarski(A_43, k10_relat_1('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_99, c_911])).
% 5.09/2.32  tff(c_951, plain, (![A_166]: (~r1_tarski(A_166, '#skF_4') | r1_tarski(A_166, k10_relat_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_927])).
% 5.09/2.32  tff(c_28, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.09/2.32  tff(c_978, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_951, c_28])).
% 5.09/2.32  tff(c_996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_978])).
% 5.09/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.32  
% 5.09/2.32  Inference rules
% 5.09/2.32  ----------------------
% 5.09/2.32  #Ref     : 0
% 5.09/2.32  #Sup     : 224
% 5.09/2.32  #Fact    : 0
% 5.09/2.32  #Define  : 0
% 5.09/2.32  #Split   : 4
% 5.09/2.32  #Chain   : 0
% 5.09/2.32  #Close   : 0
% 5.09/2.32  
% 5.09/2.32  Ordering : KBO
% 5.09/2.32  
% 5.09/2.32  Simplification rules
% 5.09/2.32  ----------------------
% 5.09/2.32  #Subsume      : 52
% 5.09/2.32  #Demod        : 24
% 5.09/2.32  #Tautology    : 3
% 5.09/2.32  #SimpNegUnit  : 0
% 5.09/2.32  #BackRed      : 0
% 5.09/2.32  
% 5.09/2.32  #Partial instantiations: 0
% 5.09/2.32  #Strategies tried      : 1
% 5.09/2.32  
% 5.09/2.32  Timing (in seconds)
% 5.09/2.32  ----------------------
% 5.09/2.33  Preprocessing        : 0.47
% 5.09/2.33  Parsing              : 0.25
% 5.09/2.33  CNF conversion       : 0.04
% 5.09/2.33  Main loop            : 0.91
% 5.09/2.33  Inferencing          : 0.32
% 5.09/2.33  Reduction            : 0.21
% 5.09/2.33  Demodulation         : 0.14
% 5.09/2.33  BG Simplification    : 0.04
% 5.09/2.33  Subsumption          : 0.28
% 5.09/2.33  Abstraction          : 0.04
% 5.09/2.33  MUC search           : 0.00
% 5.09/2.33  Cooper               : 0.00
% 5.09/2.33  Total                : 1.44
% 5.09/2.33  Index Insertion      : 0.00
% 5.09/2.33  Index Deletion       : 0.00
% 5.09/2.33  Index Matching       : 0.00
% 5.09/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
