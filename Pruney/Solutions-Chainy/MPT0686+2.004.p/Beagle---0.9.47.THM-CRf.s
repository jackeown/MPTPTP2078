%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 161 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,k3_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [A_32,B_33,B_2] :
      ( ~ r1_xboole_0(A_32,B_33)
      | r1_tarski(k3_xboole_0(A_32,B_33),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [C_21,A_19,B_20] :
      ( r1_tarski(k10_relat_1(C_21,A_19),k10_relat_1(C_21,B_20))
      | ~ r1_tarski(A_19,B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75,plain,(
    ! [B_49,A_50] :
      ( k10_relat_1(B_49,A_50) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_49),A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,(
    ! [B_51] :
      ( k10_relat_1(B_51,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_85,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_171,plain,(
    ! [C_69,A_70,B_71] :
      ( k3_xboole_0(k10_relat_1(C_69,A_70),k10_relat_1(C_69,B_71)) = k10_relat_1(C_69,k3_xboole_0(A_70,B_71))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_194,plain,(
    ! [A_70] :
      ( k3_xboole_0(k10_relat_1('#skF_3',A_70),k1_xboole_0) = k10_relat_1('#skF_3',k3_xboole_0(A_70,k1_xboole_0))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_171])).

tff(c_268,plain,(
    ! [A_75] : k3_xboole_0(k10_relat_1('#skF_3',A_75),k1_xboole_0) = k10_relat_1('#skF_3',k3_xboole_0(A_75,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_194])).

tff(c_71,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_56,B_57),B_58)
      | ~ r1_tarski(A_56,B_58)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_121,plain,(
    ! [A_6,B_7,A_56,B_57] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r1_tarski(A_56,k3_xboole_0(A_6,B_7))
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_103,c_10])).

tff(c_273,plain,(
    ! [A_75,A_56,B_57] :
      ( ~ r1_xboole_0(k10_relat_1('#skF_3',A_75),k1_xboole_0)
      | ~ r1_tarski(A_56,k10_relat_1('#skF_3',k3_xboole_0(A_75,k1_xboole_0)))
      | r1_tarski(A_56,B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_121])).

tff(c_569,plain,(
    ! [A_95,A_96,B_97] :
      ( ~ r1_tarski(A_95,k10_relat_1('#skF_3',k3_xboole_0(A_96,k1_xboole_0)))
      | r1_tarski(A_95,B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_273])).

tff(c_590,plain,(
    ! [A_19,B_97,A_96] :
      ( r1_tarski(k10_relat_1('#skF_3',A_19),B_97)
      | ~ r1_tarski(A_19,k3_xboole_0(A_96,k1_xboole_0))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_569])).

tff(c_642,plain,(
    ! [A_102,B_103,A_104] :
      ( r1_tarski(k10_relat_1('#skF_3',A_102),B_103)
      | ~ r1_tarski(A_102,k3_xboole_0(A_104,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_590])).

tff(c_676,plain,(
    ! [A_32,B_33,B_103] :
      ( r1_tarski(k10_relat_1('#skF_3',k3_xboole_0(A_32,B_33)),B_103)
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_49,c_642])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_903,plain,(
    ! [C_118,A_119,B_120] :
      ( r2_hidden('#skF_2'(k10_relat_1(C_118,A_119),k10_relat_1(C_118,B_120)),k10_relat_1(C_118,k3_xboole_0(A_119,B_120)))
      | r1_xboole_0(k10_relat_1(C_118,A_119),k10_relat_1(C_118,B_120))
      | ~ v1_funct_1(C_118)
      | ~ v1_relat_1(C_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2439,plain,(
    ! [C_185,A_186,B_187,B_188] :
      ( r2_hidden('#skF_2'(k10_relat_1(C_185,A_186),k10_relat_1(C_185,B_187)),B_188)
      | ~ r1_tarski(k10_relat_1(C_185,k3_xboole_0(A_186,B_187)),B_188)
      | r1_xboole_0(k10_relat_1(C_185,A_186),k10_relat_1(C_185,B_187))
      | ~ v1_funct_1(C_185)
      | ~ v1_relat_1(C_185) ) ),
    inference(resolution,[status(thm)],[c_903,c_2])).

tff(c_50,plain,(
    ! [A_35,C_36,B_37] :
      ( ~ r2_hidden(A_35,C_36)
      | ~ r1_xboole_0(k2_tarski(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    ! [A_35] : ~ r2_hidden(A_35,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_3223,plain,(
    ! [C_215,A_216,B_217] :
      ( ~ r1_tarski(k10_relat_1(C_215,k3_xboole_0(A_216,B_217)),k1_xboole_0)
      | r1_xboole_0(k10_relat_1(C_215,A_216),k10_relat_1(C_215,B_217))
      | ~ v1_funct_1(C_215)
      | ~ v1_relat_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_2439,c_55])).

tff(c_26,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_3','#skF_4'),k10_relat_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3230,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3223,c_26])).

tff(c_3265,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3230])).

tff(c_3288,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_676,c_3265])).

tff(c_3295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.83  
% 4.43/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.83  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.43/1.83  
% 4.43/1.83  %Foreground sorts:
% 4.43/1.83  
% 4.43/1.83  
% 4.43/1.83  %Background operators:
% 4.43/1.83  
% 4.43/1.83  
% 4.43/1.83  %Foreground operators:
% 4.43/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.43/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.43/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.43/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.43/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.43/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.43/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.83  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.43/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.43/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.43/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.43/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.43/1.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.43/1.83  
% 4.43/1.85  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_funct_1)).
% 4.43/1.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.43/1.85  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.43/1.85  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 4.43/1.85  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.43/1.85  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 4.43/1.85  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 4.43/1.85  tff(f_53, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.43/1.85  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.85  tff(c_44, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.43/1.85  tff(c_49, plain, (![A_32, B_33, B_2]: (~r1_xboole_0(A_32, B_33) | r1_tarski(k3_xboole_0(A_32, B_33), B_2))), inference(resolution, [status(thm)], [c_6, c_44])).
% 4.43/1.85  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.85  tff(c_22, plain, (![C_21, A_19, B_20]: (r1_tarski(k10_relat_1(C_21, A_19), k10_relat_1(C_21, B_20)) | ~r1_tarski(A_19, B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.43/1.85  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.43/1.85  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.85  tff(c_75, plain, (![B_49, A_50]: (k10_relat_1(B_49, A_50)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_49), A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.43/1.85  tff(c_81, plain, (![B_51]: (k10_relat_1(B_51, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_12, c_75])).
% 4.43/1.85  tff(c_85, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_81])).
% 4.43/1.85  tff(c_171, plain, (![C_69, A_70, B_71]: (k3_xboole_0(k10_relat_1(C_69, A_70), k10_relat_1(C_69, B_71))=k10_relat_1(C_69, k3_xboole_0(A_70, B_71)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.43/1.85  tff(c_194, plain, (![A_70]: (k3_xboole_0(k10_relat_1('#skF_3', A_70), k1_xboole_0)=k10_relat_1('#skF_3', k3_xboole_0(A_70, k1_xboole_0)) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_171])).
% 4.43/1.85  tff(c_268, plain, (![A_75]: (k3_xboole_0(k10_relat_1('#skF_3', A_75), k1_xboole_0)=k10_relat_1('#skF_3', k3_xboole_0(A_75, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_194])).
% 4.43/1.85  tff(c_71, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.85  tff(c_103, plain, (![A_56, B_57, B_58]: (r2_hidden('#skF_1'(A_56, B_57), B_58) | ~r1_tarski(A_56, B_58) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_6, c_71])).
% 4.43/1.85  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.43/1.85  tff(c_121, plain, (![A_6, B_7, A_56, B_57]: (~r1_xboole_0(A_6, B_7) | ~r1_tarski(A_56, k3_xboole_0(A_6, B_7)) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_103, c_10])).
% 4.43/1.85  tff(c_273, plain, (![A_75, A_56, B_57]: (~r1_xboole_0(k10_relat_1('#skF_3', A_75), k1_xboole_0) | ~r1_tarski(A_56, k10_relat_1('#skF_3', k3_xboole_0(A_75, k1_xboole_0))) | r1_tarski(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_268, c_121])).
% 4.43/1.85  tff(c_569, plain, (![A_95, A_96, B_97]: (~r1_tarski(A_95, k10_relat_1('#skF_3', k3_xboole_0(A_96, k1_xboole_0))) | r1_tarski(A_95, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_273])).
% 4.43/1.85  tff(c_590, plain, (![A_19, B_97, A_96]: (r1_tarski(k10_relat_1('#skF_3', A_19), B_97) | ~r1_tarski(A_19, k3_xboole_0(A_96, k1_xboole_0)) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_569])).
% 4.43/1.85  tff(c_642, plain, (![A_102, B_103, A_104]: (r1_tarski(k10_relat_1('#skF_3', A_102), B_103) | ~r1_tarski(A_102, k3_xboole_0(A_104, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_590])).
% 4.43/1.85  tff(c_676, plain, (![A_32, B_33, B_103]: (r1_tarski(k10_relat_1('#skF_3', k3_xboole_0(A_32, B_33)), B_103) | ~r1_xboole_0(A_32, B_33))), inference(resolution, [status(thm)], [c_49, c_642])).
% 4.43/1.85  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.43/1.85  tff(c_903, plain, (![C_118, A_119, B_120]: (r2_hidden('#skF_2'(k10_relat_1(C_118, A_119), k10_relat_1(C_118, B_120)), k10_relat_1(C_118, k3_xboole_0(A_119, B_120))) | r1_xboole_0(k10_relat_1(C_118, A_119), k10_relat_1(C_118, B_120)) | ~v1_funct_1(C_118) | ~v1_relat_1(C_118))), inference(superposition, [status(thm), theory('equality')], [c_171, c_8])).
% 4.43/1.85  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.43/1.85  tff(c_2439, plain, (![C_185, A_186, B_187, B_188]: (r2_hidden('#skF_2'(k10_relat_1(C_185, A_186), k10_relat_1(C_185, B_187)), B_188) | ~r1_tarski(k10_relat_1(C_185, k3_xboole_0(A_186, B_187)), B_188) | r1_xboole_0(k10_relat_1(C_185, A_186), k10_relat_1(C_185, B_187)) | ~v1_funct_1(C_185) | ~v1_relat_1(C_185))), inference(resolution, [status(thm)], [c_903, c_2])).
% 4.43/1.85  tff(c_50, plain, (![A_35, C_36, B_37]: (~r2_hidden(A_35, C_36) | ~r1_xboole_0(k2_tarski(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.43/1.85  tff(c_55, plain, (![A_35]: (~r2_hidden(A_35, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_50])).
% 4.43/1.85  tff(c_3223, plain, (![C_215, A_216, B_217]: (~r1_tarski(k10_relat_1(C_215, k3_xboole_0(A_216, B_217)), k1_xboole_0) | r1_xboole_0(k10_relat_1(C_215, A_216), k10_relat_1(C_215, B_217)) | ~v1_funct_1(C_215) | ~v1_relat_1(C_215))), inference(resolution, [status(thm)], [c_2439, c_55])).
% 4.43/1.85  tff(c_26, plain, (~r1_xboole_0(k10_relat_1('#skF_3', '#skF_4'), k10_relat_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.85  tff(c_3230, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3223, c_26])).
% 4.43/1.85  tff(c_3265, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3230])).
% 4.43/1.85  tff(c_3288, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_676, c_3265])).
% 4.43/1.85  tff(c_3295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3288])).
% 4.43/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.85  
% 4.43/1.85  Inference rules
% 4.43/1.85  ----------------------
% 4.43/1.85  #Ref     : 0
% 4.43/1.85  #Sup     : 780
% 4.43/1.85  #Fact    : 0
% 4.43/1.85  #Define  : 0
% 4.43/1.85  #Split   : 0
% 4.43/1.85  #Chain   : 0
% 4.43/1.85  #Close   : 0
% 4.43/1.85  
% 4.43/1.85  Ordering : KBO
% 4.43/1.85  
% 4.43/1.85  Simplification rules
% 4.43/1.85  ----------------------
% 4.43/1.85  #Subsume      : 217
% 4.43/1.85  #Demod        : 610
% 4.43/1.85  #Tautology    : 233
% 4.43/1.85  #SimpNegUnit  : 5
% 4.43/1.85  #BackRed      : 0
% 4.43/1.85  
% 4.43/1.85  #Partial instantiations: 0
% 4.43/1.85  #Strategies tried      : 1
% 4.43/1.85  
% 4.43/1.85  Timing (in seconds)
% 4.43/1.85  ----------------------
% 4.43/1.85  Preprocessing        : 0.30
% 4.43/1.85  Parsing              : 0.17
% 4.43/1.85  CNF conversion       : 0.02
% 4.43/1.85  Main loop            : 0.74
% 4.43/1.85  Inferencing          : 0.24
% 4.43/1.85  Reduction            : 0.27
% 4.43/1.85  Demodulation         : 0.20
% 4.43/1.85  BG Simplification    : 0.02
% 4.43/1.85  Subsumption          : 0.16
% 4.43/1.85  Abstraction          : 0.03
% 4.43/1.85  MUC search           : 0.00
% 4.43/1.85  Cooper               : 0.00
% 4.43/1.85  Total                : 1.07
% 4.43/1.85  Index Insertion      : 0.00
% 4.43/1.85  Index Deletion       : 0.00
% 4.43/1.85  Index Matching       : 0.00
% 4.43/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
