%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:43 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 321 expanded)
%              Number of leaves         :   26 ( 127 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 949 expanded)
%              Number of equality atoms :   24 ( 239 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [A_31] :
      ( k4_relat_1(A_31) = k2_funct_1(A_31)
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_45,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_48,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_45])).

tff(c_14,plain,(
    ! [A_18] :
      ( v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_56,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_18,plain,(
    ! [A_20] :
      ( v1_funct_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [A_25,C_27] :
      ( r2_hidden(k4_tarski(A_25,k1_funct_1(C_27,A_25)),C_27)
      | ~ r2_hidden(A_25,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,(
    ! [C_45,D_46,A_47] :
      ( r2_hidden(k4_tarski(C_45,D_46),k4_relat_1(A_47))
      | ~ r2_hidden(k4_tarski(D_46,C_45),A_47)
      | ~ v1_relat_1(k4_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [C_45,D_46] :
      ( r2_hidden(k4_tarski(C_45,D_46),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_46,C_45),'#skF_6')
      | ~ v1_relat_1(k4_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_90])).

tff(c_108,plain,(
    ! [C_48,D_49] :
      ( r2_hidden(k4_tarski(C_48,D_49),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_49,C_48),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_48,c_102])).

tff(c_28,plain,(
    ! [A_25,C_27,B_26] :
      ( r2_hidden(A_25,k1_relat_1(C_27))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,(
    ! [C_48,D_49] :
      ( r2_hidden(C_48,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_49,C_48),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_108,c_28])).

tff(c_121,plain,(
    ! [C_48,D_49] :
      ( r2_hidden(C_48,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_49,C_48),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_114])).

tff(c_125,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_128,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_128])).

tff(c_134,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_26,plain,(
    ! [C_27,A_25,B_26] :
      ( k1_funct_1(C_27,A_25) = B_26
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_117,plain,(
    ! [C_48,D_49] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_48) = D_49
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_49,C_48),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_108,c_26])).

tff(c_124,plain,(
    ! [C_48,D_49] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_48) = D_49
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_49,C_48),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117])).

tff(c_145,plain,(
    ! [C_53,D_54] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_53) = D_54
      | ~ r2_hidden(k4_tarski(D_54,C_53),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_124])).

tff(c_149,plain,(
    ! [A_25] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_25)) = A_25
      | ~ r2_hidden(A_25,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_145])).

tff(c_168,plain,(
    ! [A_58] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_58)) = A_58
      | ~ r2_hidden(A_58,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_149])).

tff(c_30,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_177,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_58])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_177])).

tff(c_189,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_196,plain,(
    ! [A_65,C_66] :
      ( r2_hidden(k4_tarski(A_65,k1_funct_1(C_66,A_65)),C_66)
      | ~ r2_hidden(A_65,k1_relat_1(C_66))
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_205,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_5'),'#skF_5'),k2_funct_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_196])).

tff(c_210,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_5'),'#skF_5'),k2_funct_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_205])).

tff(c_275,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_278,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_275])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_278])).

tff(c_284,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_294,plain,(
    ! [B_80,C_81,A_82] :
      ( k1_funct_1(k5_relat_1(B_80,C_81),A_82) = k1_funct_1(C_81,k1_funct_1(B_80,A_82))
      | ~ r2_hidden(A_82,k1_relat_1(B_80))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_301,plain,(
    ! [C_81] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_81),'#skF_5') = k1_funct_1(C_81,k1_funct_1('#skF_6','#skF_5'))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_294])).

tff(c_345,plain,(
    ! [C_86] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_86),'#skF_5') = k1_funct_1(C_86,k1_funct_1('#skF_6','#skF_5'))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_301])).

tff(c_188,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_354,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5'
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_188])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_284,c_189,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.28  
% 2.31/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.28  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.31/1.28  
% 2.31/1.28  %Foreground sorts:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Background operators:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Foreground operators:
% 2.31/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.31/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.31/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.31/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.28  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.31/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.31/1.28  
% 2.31/1.30  tff(f_93, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 2.31/1.30  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.31/1.30  tff(f_41, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.31/1.30  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.31/1.30  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.31/1.30  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 2.31/1.30  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.31/1.30  tff(c_38, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.31/1.30  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.31/1.30  tff(c_34, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.31/1.30  tff(c_42, plain, (![A_31]: (k4_relat_1(A_31)=k2_funct_1(A_31) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.30  tff(c_45, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.31/1.30  tff(c_48, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_45])).
% 2.31/1.30  tff(c_14, plain, (![A_18]: (v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.30  tff(c_52, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_48, c_14])).
% 2.31/1.30  tff(c_56, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.31/1.30  tff(c_18, plain, (![A_20]: (v1_funct_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.31/1.30  tff(c_32, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.31/1.30  tff(c_24, plain, (![A_25, C_27]: (r2_hidden(k4_tarski(A_25, k1_funct_1(C_27, A_25)), C_27) | ~r2_hidden(A_25, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.31/1.30  tff(c_90, plain, (![C_45, D_46, A_47]: (r2_hidden(k4_tarski(C_45, D_46), k4_relat_1(A_47)) | ~r2_hidden(k4_tarski(D_46, C_45), A_47) | ~v1_relat_1(k4_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.30  tff(c_102, plain, (![C_45, D_46]: (r2_hidden(k4_tarski(C_45, D_46), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_46, C_45), '#skF_6') | ~v1_relat_1(k4_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_90])).
% 2.31/1.30  tff(c_108, plain, (![C_48, D_49]: (r2_hidden(k4_tarski(C_48, D_49), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_49, C_48), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_48, c_102])).
% 2.31/1.30  tff(c_28, plain, (![A_25, C_27, B_26]: (r2_hidden(A_25, k1_relat_1(C_27)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.31/1.30  tff(c_114, plain, (![C_48, D_49]: (r2_hidden(C_48, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_49, C_48), '#skF_6'))), inference(resolution, [status(thm)], [c_108, c_28])).
% 2.31/1.30  tff(c_121, plain, (![C_48, D_49]: (r2_hidden(C_48, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_49, C_48), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_114])).
% 2.31/1.30  tff(c_125, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_121])).
% 2.31/1.30  tff(c_128, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_125])).
% 2.31/1.30  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_128])).
% 2.31/1.30  tff(c_134, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_121])).
% 2.31/1.30  tff(c_26, plain, (![C_27, A_25, B_26]: (k1_funct_1(C_27, A_25)=B_26 | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.31/1.30  tff(c_117, plain, (![C_48, D_49]: (k1_funct_1(k2_funct_1('#skF_6'), C_48)=D_49 | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_49, C_48), '#skF_6'))), inference(resolution, [status(thm)], [c_108, c_26])).
% 2.31/1.30  tff(c_124, plain, (![C_48, D_49]: (k1_funct_1(k2_funct_1('#skF_6'), C_48)=D_49 | ~v1_funct_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_49, C_48), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117])).
% 2.31/1.30  tff(c_145, plain, (![C_53, D_54]: (k1_funct_1(k2_funct_1('#skF_6'), C_53)=D_54 | ~r2_hidden(k4_tarski(D_54, C_53), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_124])).
% 2.31/1.30  tff(c_149, plain, (![A_25]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_25))=A_25 | ~r2_hidden(A_25, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_145])).
% 2.31/1.30  tff(c_168, plain, (![A_58]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_58))=A_58 | ~r2_hidden(A_58, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_149])).
% 2.31/1.30  tff(c_30, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.31/1.30  tff(c_58, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_30])).
% 2.31/1.30  tff(c_177, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_58])).
% 2.31/1.30  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_177])).
% 2.31/1.30  tff(c_189, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_30])).
% 2.31/1.30  tff(c_196, plain, (![A_65, C_66]: (r2_hidden(k4_tarski(A_65, k1_funct_1(C_66, A_65)), C_66) | ~r2_hidden(A_65, k1_relat_1(C_66)) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.31/1.30  tff(c_205, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_5'), '#skF_5'), k2_funct_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_196])).
% 2.31/1.30  tff(c_210, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_5'), '#skF_5'), k2_funct_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_205])).
% 2.31/1.30  tff(c_275, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_210])).
% 2.31/1.30  tff(c_278, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_275])).
% 2.31/1.30  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_278])).
% 2.31/1.30  tff(c_284, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_210])).
% 2.31/1.30  tff(c_294, plain, (![B_80, C_81, A_82]: (k1_funct_1(k5_relat_1(B_80, C_81), A_82)=k1_funct_1(C_81, k1_funct_1(B_80, A_82)) | ~r2_hidden(A_82, k1_relat_1(B_80)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.30  tff(c_301, plain, (![C_81]: (k1_funct_1(k5_relat_1('#skF_6', C_81), '#skF_5')=k1_funct_1(C_81, k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_294])).
% 2.31/1.30  tff(c_345, plain, (![C_86]: (k1_funct_1(k5_relat_1('#skF_6', C_86), '#skF_5')=k1_funct_1(C_86, k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_301])).
% 2.31/1.30  tff(c_188, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_30])).
% 2.31/1.30  tff(c_354, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5' | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_345, c_188])).
% 2.31/1.30  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_284, c_189, c_354])).
% 2.31/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.30  
% 2.31/1.30  Inference rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Ref     : 0
% 2.31/1.30  #Sup     : 57
% 2.31/1.30  #Fact    : 0
% 2.31/1.30  #Define  : 0
% 2.31/1.30  #Split   : 4
% 2.31/1.30  #Chain   : 0
% 2.31/1.30  #Close   : 0
% 2.31/1.30  
% 2.31/1.30  Ordering : KBO
% 2.31/1.30  
% 2.31/1.30  Simplification rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Subsume      : 0
% 2.31/1.30  #Demod        : 57
% 2.31/1.30  #Tautology    : 19
% 2.31/1.30  #SimpNegUnit  : 0
% 2.31/1.30  #BackRed      : 0
% 2.31/1.30  
% 2.31/1.30  #Partial instantiations: 0
% 2.31/1.30  #Strategies tried      : 1
% 2.31/1.30  
% 2.31/1.30  Timing (in seconds)
% 2.31/1.30  ----------------------
% 2.31/1.30  Preprocessing        : 0.31
% 2.31/1.30  Parsing              : 0.16
% 2.31/1.30  CNF conversion       : 0.02
% 2.31/1.30  Main loop            : 0.23
% 2.31/1.30  Inferencing          : 0.09
% 2.31/1.30  Reduction            : 0.07
% 2.31/1.30  Demodulation         : 0.05
% 2.31/1.30  BG Simplification    : 0.02
% 2.31/1.30  Subsumption          : 0.04
% 2.31/1.30  Abstraction          : 0.01
% 2.31/1.30  MUC search           : 0.00
% 2.31/1.30  Cooper               : 0.00
% 2.31/1.30  Total                : 0.58
% 2.31/1.30  Index Insertion      : 0.00
% 2.31/1.30  Index Deletion       : 0.00
% 2.31/1.30  Index Matching       : 0.00
% 2.31/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
