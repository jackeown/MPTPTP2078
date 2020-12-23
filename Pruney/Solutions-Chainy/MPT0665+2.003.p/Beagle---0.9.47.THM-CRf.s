%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:14 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 266 expanded)
%              Number of leaves         :   33 ( 109 expanded)
%              Depth                    :   19
%              Number of atoms          :  139 ( 780 expanded)
%              Number of equality atoms :   17 (  79 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [A_81,B_82] :
      ( v1_funct_1(k7_relat_1(A_81,B_82))
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,(
    r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k7_relat_1(A_39,B_40))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    r2_hidden('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [C_35,A_20] :
      ( r2_hidden(k4_tarski(C_35,'#skF_8'(A_20,k1_relat_1(A_20),C_35)),A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [C_97,A_98,B_99] :
      ( k1_funct_1(C_97,A_98) = B_99
      | ~ r2_hidden(k4_tarski(A_98,B_99),C_97)
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_145,plain,(
    ! [A_118,C_119] :
      ( '#skF_8'(A_118,k1_relat_1(A_118),C_119) = k1_funct_1(A_118,C_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118)
      | ~ r2_hidden(C_119,k1_relat_1(A_118)) ) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_158,plain,
    ( '#skF_8'('#skF_15',k1_relat_1('#skF_15'),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
    | ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_66,c_145])).

tff(c_165,plain,(
    '#skF_8'('#skF_15',k1_relat_1('#skF_15'),'#skF_13') = k1_funct_1('#skF_15','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_158])).

tff(c_169,plain,
    ( r2_hidden(k4_tarski('#skF_13',k1_funct_1('#skF_15','#skF_13')),'#skF_15')
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_20])).

tff(c_173,plain,(
    r2_hidden(k4_tarski('#skF_13',k1_funct_1('#skF_15','#skF_13')),'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_169])).

tff(c_377,plain,(
    ! [D_143,E_144,A_145,B_146] :
      ( r2_hidden(k4_tarski(D_143,E_144),k7_relat_1(A_145,B_146))
      | ~ r2_hidden(k4_tarski(D_143,E_144),A_145)
      | ~ r2_hidden(D_143,B_146)
      | ~ v1_relat_1(k7_relat_1(A_145,B_146))
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [C_85,A_83,B_84] :
      ( k1_funct_1(C_85,A_83) = B_84
      | ~ r2_hidden(k4_tarski(A_83,B_84),C_85)
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_512,plain,(
    ! [A_164,B_165,D_166,E_167] :
      ( k1_funct_1(k7_relat_1(A_164,B_165),D_166) = E_167
      | ~ v1_funct_1(k7_relat_1(A_164,B_165))
      | ~ r2_hidden(k4_tarski(D_166,E_167),A_164)
      | ~ r2_hidden(D_166,B_165)
      | ~ v1_relat_1(k7_relat_1(A_164,B_165))
      | ~ v1_relat_1(A_164) ) ),
    inference(resolution,[status(thm)],[c_377,c_58])).

tff(c_523,plain,(
    ! [B_165] :
      ( k1_funct_1(k7_relat_1('#skF_15',B_165),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
      | ~ v1_funct_1(k7_relat_1('#skF_15',B_165))
      | ~ r2_hidden('#skF_13',B_165)
      | ~ v1_relat_1(k7_relat_1('#skF_15',B_165))
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_173,c_512])).

tff(c_537,plain,(
    ! [B_168] :
      ( k1_funct_1(k7_relat_1('#skF_15',B_168),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
      | ~ v1_funct_1(k7_relat_1('#skF_15',B_168))
      | ~ r2_hidden('#skF_13',B_168)
      | ~ v1_relat_1(k7_relat_1('#skF_15',B_168)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_523])).

tff(c_541,plain,(
    ! [B_40] :
      ( k1_funct_1(k7_relat_1('#skF_15',B_40),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
      | ~ v1_funct_1(k7_relat_1('#skF_15',B_40))
      | ~ r2_hidden('#skF_13',B_40)
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_32,c_537])).

tff(c_545,plain,(
    ! [B_169] :
      ( k1_funct_1(k7_relat_1('#skF_15',B_169),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
      | ~ v1_funct_1(k7_relat_1('#skF_15',B_169))
      | ~ r2_hidden('#skF_13',B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_541])).

tff(c_549,plain,(
    ! [B_82] :
      ( k1_funct_1(k7_relat_1('#skF_15',B_82),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
      | ~ r2_hidden('#skF_13',B_82)
      | ~ v1_funct_1('#skF_15')
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_52,c_545])).

tff(c_587,plain,(
    ! [B_173] :
      ( k1_funct_1(k7_relat_1('#skF_15',B_173),'#skF_13') = k1_funct_1('#skF_15','#skF_13')
      | ~ r2_hidden('#skF_13',B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_549])).

tff(c_34,plain,(
    ! [A_41,D_80] :
      ( r2_hidden(k1_funct_1(A_41,D_80),k2_relat_1(A_41))
      | ~ r2_hidden(D_80,k1_relat_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_655,plain,(
    ! [B_179] :
      ( r2_hidden(k1_funct_1('#skF_15','#skF_13'),k2_relat_1(k7_relat_1('#skF_15',B_179)))
      | ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15',B_179)))
      | ~ v1_funct_1(k7_relat_1('#skF_15',B_179))
      | ~ v1_relat_1(k7_relat_1('#skF_15',B_179))
      | ~ r2_hidden('#skF_13',B_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_34])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_15','#skF_13'),k2_relat_1(k7_relat_1('#skF_15','#skF_14'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_658,plain,
    ( ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14')))
    | ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ r2_hidden('#skF_13','#skF_14') ),
    inference(resolution,[status(thm)],[c_655,c_62])).

tff(c_661,plain,
    ( ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14')))
    | ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_658])).

tff(c_662,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_661])).

tff(c_665,plain,(
    ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_32,c_662])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_665])).

tff(c_671,plain,(
    v1_relat_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_22,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k1_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(C_35,D_38),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_398,plain,(
    ! [D_147,A_148,B_149,E_150] :
      ( r2_hidden(D_147,k1_relat_1(k7_relat_1(A_148,B_149)))
      | ~ r2_hidden(k4_tarski(D_147,E_150),A_148)
      | ~ r2_hidden(D_147,B_149)
      | ~ v1_relat_1(k7_relat_1(A_148,B_149))
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_377,c_22])).

tff(c_418,plain,(
    ! [C_35,A_20,B_149] :
      ( r2_hidden(C_35,k1_relat_1(k7_relat_1(A_20,B_149)))
      | ~ r2_hidden(C_35,B_149)
      | ~ v1_relat_1(k7_relat_1(A_20,B_149))
      | ~ v1_relat_1(A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_20,c_398])).

tff(c_670,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14'))) ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_672,plain,(
    ~ r2_hidden('#skF_13',k1_relat_1(k7_relat_1('#skF_15','#skF_14'))) ),
    inference(splitLeft,[status(thm)],[c_670])).

tff(c_675,plain,
    ( ~ r2_hidden('#skF_13','#skF_14')
    | ~ v1_relat_1(k7_relat_1('#skF_15','#skF_14'))
    | ~ v1_relat_1('#skF_15')
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_418,c_672])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_671,c_64,c_675])).

tff(c_683,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_15','#skF_14')) ),
    inference(splitRight,[status(thm)],[c_670])).

tff(c_696,plain,
    ( ~ v1_funct_1('#skF_15')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_52,c_683])).

tff(c_700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.45  
% 3.17/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.46  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5
% 3.17/1.46  
% 3.17/1.46  %Foreground sorts:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Background operators:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Foreground operators:
% 3.17/1.46  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 3.17/1.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.17/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.17/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.46  tff('#skF_15', type, '#skF_15': $i).
% 3.17/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.17/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.17/1.46  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 3.17/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.17/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.46  tff('#skF_14', type, '#skF_14': $i).
% 3.17/1.46  tff('#skF_13', type, '#skF_13': $i).
% 3.17/1.46  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.17/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.17/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.46  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.17/1.46  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.17/1.46  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.17/1.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.17/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.46  
% 3.22/1.47  tff(f_95, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 3.22/1.47  tff(f_74, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.22/1.47  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.22/1.47  tff(f_47, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.22/1.47  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.22/1.47  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 3.22/1.47  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.22/1.47  tff(c_70, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.47  tff(c_68, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.47  tff(c_52, plain, (![A_81, B_82]: (v1_funct_1(k7_relat_1(A_81, B_82)) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.22/1.47  tff(c_66, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.47  tff(c_32, plain, (![A_39, B_40]: (v1_relat_1(k7_relat_1(A_39, B_40)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.47  tff(c_64, plain, (r2_hidden('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.47  tff(c_20, plain, (![C_35, A_20]: (r2_hidden(k4_tarski(C_35, '#skF_8'(A_20, k1_relat_1(A_20), C_35)), A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.47  tff(c_80, plain, (![C_97, A_98, B_99]: (k1_funct_1(C_97, A_98)=B_99 | ~r2_hidden(k4_tarski(A_98, B_99), C_97) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.47  tff(c_145, plain, (![A_118, C_119]: ('#skF_8'(A_118, k1_relat_1(A_118), C_119)=k1_funct_1(A_118, C_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118) | ~r2_hidden(C_119, k1_relat_1(A_118)))), inference(resolution, [status(thm)], [c_20, c_80])).
% 3.22/1.47  tff(c_158, plain, ('#skF_8'('#skF_15', k1_relat_1('#skF_15'), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_66, c_145])).
% 3.22/1.47  tff(c_165, plain, ('#skF_8'('#skF_15', k1_relat_1('#skF_15'), '#skF_13')=k1_funct_1('#skF_15', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_158])).
% 3.22/1.47  tff(c_169, plain, (r2_hidden(k4_tarski('#skF_13', k1_funct_1('#skF_15', '#skF_13')), '#skF_15') | ~r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_20])).
% 3.22/1.47  tff(c_173, plain, (r2_hidden(k4_tarski('#skF_13', k1_funct_1('#skF_15', '#skF_13')), '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_169])).
% 3.22/1.47  tff(c_377, plain, (![D_143, E_144, A_145, B_146]: (r2_hidden(k4_tarski(D_143, E_144), k7_relat_1(A_145, B_146)) | ~r2_hidden(k4_tarski(D_143, E_144), A_145) | ~r2_hidden(D_143, B_146) | ~v1_relat_1(k7_relat_1(A_145, B_146)) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.47  tff(c_58, plain, (![C_85, A_83, B_84]: (k1_funct_1(C_85, A_83)=B_84 | ~r2_hidden(k4_tarski(A_83, B_84), C_85) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.47  tff(c_512, plain, (![A_164, B_165, D_166, E_167]: (k1_funct_1(k7_relat_1(A_164, B_165), D_166)=E_167 | ~v1_funct_1(k7_relat_1(A_164, B_165)) | ~r2_hidden(k4_tarski(D_166, E_167), A_164) | ~r2_hidden(D_166, B_165) | ~v1_relat_1(k7_relat_1(A_164, B_165)) | ~v1_relat_1(A_164))), inference(resolution, [status(thm)], [c_377, c_58])).
% 3.22/1.47  tff(c_523, plain, (![B_165]: (k1_funct_1(k7_relat_1('#skF_15', B_165), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~v1_funct_1(k7_relat_1('#skF_15', B_165)) | ~r2_hidden('#skF_13', B_165) | ~v1_relat_1(k7_relat_1('#skF_15', B_165)) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_173, c_512])).
% 3.22/1.47  tff(c_537, plain, (![B_168]: (k1_funct_1(k7_relat_1('#skF_15', B_168), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~v1_funct_1(k7_relat_1('#skF_15', B_168)) | ~r2_hidden('#skF_13', B_168) | ~v1_relat_1(k7_relat_1('#skF_15', B_168)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_523])).
% 3.22/1.47  tff(c_541, plain, (![B_40]: (k1_funct_1(k7_relat_1('#skF_15', B_40), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~v1_funct_1(k7_relat_1('#skF_15', B_40)) | ~r2_hidden('#skF_13', B_40) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_32, c_537])).
% 3.22/1.47  tff(c_545, plain, (![B_169]: (k1_funct_1(k7_relat_1('#skF_15', B_169), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~v1_funct_1(k7_relat_1('#skF_15', B_169)) | ~r2_hidden('#skF_13', B_169))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_541])).
% 3.22/1.47  tff(c_549, plain, (![B_82]: (k1_funct_1(k7_relat_1('#skF_15', B_82), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~r2_hidden('#skF_13', B_82) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_52, c_545])).
% 3.22/1.47  tff(c_587, plain, (![B_173]: (k1_funct_1(k7_relat_1('#skF_15', B_173), '#skF_13')=k1_funct_1('#skF_15', '#skF_13') | ~r2_hidden('#skF_13', B_173))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_549])).
% 3.22/1.47  tff(c_34, plain, (![A_41, D_80]: (r2_hidden(k1_funct_1(A_41, D_80), k2_relat_1(A_41)) | ~r2_hidden(D_80, k1_relat_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.47  tff(c_655, plain, (![B_179]: (r2_hidden(k1_funct_1('#skF_15', '#skF_13'), k2_relat_1(k7_relat_1('#skF_15', B_179))) | ~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', B_179))) | ~v1_funct_1(k7_relat_1('#skF_15', B_179)) | ~v1_relat_1(k7_relat_1('#skF_15', B_179)) | ~r2_hidden('#skF_13', B_179))), inference(superposition, [status(thm), theory('equality')], [c_587, c_34])).
% 3.22/1.47  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_15', '#skF_13'), k2_relat_1(k7_relat_1('#skF_15', '#skF_14')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.47  tff(c_658, plain, (~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14'))) | ~v1_funct_1(k7_relat_1('#skF_15', '#skF_14')) | ~v1_relat_1(k7_relat_1('#skF_15', '#skF_14')) | ~r2_hidden('#skF_13', '#skF_14')), inference(resolution, [status(thm)], [c_655, c_62])).
% 3.22/1.47  tff(c_661, plain, (~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14'))) | ~v1_funct_1(k7_relat_1('#skF_15', '#skF_14')) | ~v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_658])).
% 3.22/1.47  tff(c_662, plain, (~v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(splitLeft, [status(thm)], [c_661])).
% 3.22/1.47  tff(c_665, plain, (~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_32, c_662])).
% 3.22/1.47  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_665])).
% 3.22/1.47  tff(c_671, plain, (v1_relat_1(k7_relat_1('#skF_15', '#skF_14'))), inference(splitRight, [status(thm)], [c_661])).
% 3.22/1.47  tff(c_22, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k1_relat_1(A_20)) | ~r2_hidden(k4_tarski(C_35, D_38), A_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.47  tff(c_398, plain, (![D_147, A_148, B_149, E_150]: (r2_hidden(D_147, k1_relat_1(k7_relat_1(A_148, B_149))) | ~r2_hidden(k4_tarski(D_147, E_150), A_148) | ~r2_hidden(D_147, B_149) | ~v1_relat_1(k7_relat_1(A_148, B_149)) | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_377, c_22])).
% 3.22/1.47  tff(c_418, plain, (![C_35, A_20, B_149]: (r2_hidden(C_35, k1_relat_1(k7_relat_1(A_20, B_149))) | ~r2_hidden(C_35, B_149) | ~v1_relat_1(k7_relat_1(A_20, B_149)) | ~v1_relat_1(A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(resolution, [status(thm)], [c_20, c_398])).
% 3.22/1.47  tff(c_670, plain, (~v1_funct_1(k7_relat_1('#skF_15', '#skF_14')) | ~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14')))), inference(splitRight, [status(thm)], [c_661])).
% 3.22/1.47  tff(c_672, plain, (~r2_hidden('#skF_13', k1_relat_1(k7_relat_1('#skF_15', '#skF_14')))), inference(splitLeft, [status(thm)], [c_670])).
% 3.22/1.47  tff(c_675, plain, (~r2_hidden('#skF_13', '#skF_14') | ~v1_relat_1(k7_relat_1('#skF_15', '#skF_14')) | ~v1_relat_1('#skF_15') | ~r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_418, c_672])).
% 3.22/1.47  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_671, c_64, c_675])).
% 3.22/1.47  tff(c_683, plain, (~v1_funct_1(k7_relat_1('#skF_15', '#skF_14'))), inference(splitRight, [status(thm)], [c_670])).
% 3.22/1.47  tff(c_696, plain, (~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_52, c_683])).
% 3.22/1.47  tff(c_700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_696])).
% 3.22/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  Inference rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Ref     : 0
% 3.22/1.47  #Sup     : 139
% 3.22/1.47  #Fact    : 0
% 3.22/1.47  #Define  : 0
% 3.22/1.47  #Split   : 2
% 3.22/1.47  #Chain   : 0
% 3.22/1.47  #Close   : 0
% 3.22/1.47  
% 3.22/1.47  Ordering : KBO
% 3.22/1.47  
% 3.22/1.47  Simplification rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Subsume      : 10
% 3.22/1.47  #Demod        : 20
% 3.22/1.47  #Tautology    : 32
% 3.22/1.47  #SimpNegUnit  : 0
% 3.22/1.47  #BackRed      : 0
% 3.22/1.47  
% 3.22/1.47  #Partial instantiations: 0
% 3.22/1.47  #Strategies tried      : 1
% 3.22/1.47  
% 3.22/1.47  Timing (in seconds)
% 3.22/1.47  ----------------------
% 3.22/1.47  Preprocessing        : 0.32
% 3.22/1.47  Parsing              : 0.16
% 3.22/1.47  CNF conversion       : 0.03
% 3.22/1.47  Main loop            : 0.39
% 3.22/1.48  Inferencing          : 0.15
% 3.22/1.48  Reduction            : 0.09
% 3.22/1.48  Demodulation         : 0.06
% 3.22/1.48  BG Simplification    : 0.03
% 3.22/1.48  Subsumption          : 0.08
% 3.22/1.48  Abstraction          : 0.02
% 3.22/1.48  MUC search           : 0.00
% 3.22/1.48  Cooper               : 0.00
% 3.22/1.48  Total                : 0.74
% 3.22/1.48  Index Insertion      : 0.00
% 3.22/1.48  Index Deletion       : 0.00
% 3.22/1.48  Index Matching       : 0.00
% 3.22/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
