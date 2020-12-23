%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:13 EST 2020

% Result     : Theorem 9.50s
% Output     : CNFRefutation 9.60s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 180 expanded)
%              Number of leaves         :   33 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  112 ( 366 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_40,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = B_57
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_60])).

tff(c_32,plain,(
    ! [A_45] :
      ( k9_relat_1(A_45,k1_relat_1(A_45)) = k2_relat_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1971,plain,(
    ! [C_154,A_155,B_156] :
      ( r1_tarski(k9_relat_1(C_154,A_155),k9_relat_1(C_154,B_156))
      | ~ r1_tarski(A_155,B_156)
      | ~ v1_relat_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11137,plain,(
    ! [A_359,B_360] :
      ( r1_tarski(k2_relat_1(A_359),k9_relat_1(A_359,B_360))
      | ~ r1_tarski(k1_relat_1(A_359),B_360)
      | ~ v1_relat_1(A_359)
      | ~ v1_relat_1(A_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1971])).

tff(c_166,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(k2_xboole_0(A_70,B_72),C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [C_71] :
      ( r1_tarski('#skF_1',C_71)
      | ~ r1_tarski(k2_relat_1('#skF_3'),C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_166])).

tff(c_11162,plain,(
    ! [B_360] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_360))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_360)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_11137,c_173])).

tff(c_11199,plain,(
    ! [B_361] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_361))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_11162])).

tff(c_11324,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6,c_11199])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11345,plain,(
    k2_xboole_0('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_11324,c_12])).

tff(c_14696,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_xboole_0('#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_11345])).

tff(c_14741,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_71,c_14696])).

tff(c_38,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,k9_relat_1(B_52,k1_relat_1(B_52))) = k9_relat_1(B_52,k10_relat_1(B_52,A_51))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_15006,plain,(
    ! [A_51] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_51)) = k3_xboole_0(A_51,k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14741,c_38])).

tff(c_15034,plain,(
    ! [A_51] : k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_51)) = k3_xboole_0(A_51,k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_15006])).

tff(c_44,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_70,plain,(
    k2_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_562,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_tarski(k2_xboole_0(A_100,C_101),k2_xboole_0(B_102,C_101))
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_683,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(A_105,k2_xboole_0(B_106,C_107))
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_562,c_10])).

tff(c_709,plain,(
    ! [A_105] :
      ( r1_tarski(A_105,k10_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_105,k10_relat_1('#skF_3','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_683])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_11344,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_11324,c_14])).

tff(c_11351,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11344,c_38])).

tff(c_11361,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_11351])).

tff(c_34,plain,(
    ! [C_48,A_46,B_47] :
      ( r1_tarski(k9_relat_1(C_48,A_46),k9_relat_1(C_48,B_47))
      | ~ r1_tarski(A_46,B_47)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11434,plain,(
    ! [B_47] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_47))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_47)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11361,c_34])).

tff(c_22175,plain,(
    ! [B_515] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_515))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_11434])).

tff(c_22248,plain,
    ( r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')))
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_709,c_22175])).

tff(c_22339,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_2',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15034,c_22248])).

tff(c_15047,plain,(
    ! [A_419] : k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_419)) = k3_xboole_0(A_419,k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_15006])).

tff(c_1407,plain,(
    ! [B_135,A_136] :
      ( r1_tarski(k9_relat_1(B_135,k10_relat_1(B_135,A_136)),A_136)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1418,plain,(
    ! [B_135,A_136] :
      ( k2_xboole_0(k9_relat_1(B_135,k10_relat_1(B_135,A_136)),A_136) = A_136
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_1407,c_12])).

tff(c_15080,plain,(
    ! [A_419] :
      ( k2_xboole_0(k3_xboole_0(A_419,k2_relat_1('#skF_3')),A_419) = A_419
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15047,c_1418])).

tff(c_15365,plain,(
    ! [A_423] : k2_xboole_0(k3_xboole_0(A_423,k2_relat_1('#skF_3')),A_423) = A_423 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_15080])).

tff(c_603,plain,(
    ! [A_100,B_102,C_101] :
      ( r1_tarski(A_100,k2_xboole_0(B_102,C_101))
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(resolution,[status(thm)],[c_562,c_10])).

tff(c_15774,plain,(
    ! [A_100,A_423] :
      ( r1_tarski(A_100,A_423)
      | ~ r1_tarski(A_100,k3_xboole_0(A_423,k2_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15365,c_603])).

tff(c_22365,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22339,c_15774])).

tff(c_22386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_22365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.50/3.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.50/3.82  
% 9.50/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.50/3.83  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 9.50/3.83  
% 9.50/3.83  %Foreground sorts:
% 9.50/3.83  
% 9.50/3.83  
% 9.50/3.83  %Background operators:
% 9.50/3.83  
% 9.50/3.83  
% 9.50/3.83  %Foreground operators:
% 9.50/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.50/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.50/3.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.50/3.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.50/3.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.50/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.50/3.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.50/3.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.50/3.83  tff('#skF_2', type, '#skF_2': $i).
% 9.50/3.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.50/3.83  tff('#skF_3', type, '#skF_3': $i).
% 9.50/3.83  tff('#skF_1', type, '#skF_1': $i).
% 9.50/3.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.50/3.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.50/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.50/3.83  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.50/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.50/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.50/3.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.50/3.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.50/3.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.50/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.50/3.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.50/3.83  
% 9.60/3.84  tff(f_98, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 9.60/3.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.60/3.84  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.60/3.84  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 9.60/3.84  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 9.60/3.84  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.60/3.84  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 9.60/3.84  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 9.60/3.84  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.60/3.84  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 9.60/3.84  tff(c_40, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.60/3.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.60/3.84  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.60/3.84  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.60/3.84  tff(c_42, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.60/3.84  tff(c_60, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=B_57 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.60/3.84  tff(c_71, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_60])).
% 9.60/3.84  tff(c_32, plain, (![A_45]: (k9_relat_1(A_45, k1_relat_1(A_45))=k2_relat_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.60/3.84  tff(c_1971, plain, (![C_154, A_155, B_156]: (r1_tarski(k9_relat_1(C_154, A_155), k9_relat_1(C_154, B_156)) | ~r1_tarski(A_155, B_156) | ~v1_relat_1(C_154))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.60/3.84  tff(c_11137, plain, (![A_359, B_360]: (r1_tarski(k2_relat_1(A_359), k9_relat_1(A_359, B_360)) | ~r1_tarski(k1_relat_1(A_359), B_360) | ~v1_relat_1(A_359) | ~v1_relat_1(A_359))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1971])).
% 9.60/3.84  tff(c_166, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(k2_xboole_0(A_70, B_72), C_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.60/3.84  tff(c_173, plain, (![C_71]: (r1_tarski('#skF_1', C_71) | ~r1_tarski(k2_relat_1('#skF_3'), C_71))), inference(superposition, [status(thm), theory('equality')], [c_71, c_166])).
% 9.60/3.84  tff(c_11162, plain, (![B_360]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_360)) | ~r1_tarski(k1_relat_1('#skF_3'), B_360) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_11137, c_173])).
% 9.60/3.84  tff(c_11199, plain, (![B_361]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_361)) | ~r1_tarski(k1_relat_1('#skF_3'), B_361))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_11162])).
% 9.60/3.84  tff(c_11324, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_11199])).
% 9.60/3.84  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.60/3.84  tff(c_11345, plain, (k2_xboole_0('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_11324, c_12])).
% 9.60/3.84  tff(c_14696, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_xboole_0('#skF_1', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_11345])).
% 9.60/3.84  tff(c_14741, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_71, c_14696])).
% 9.60/3.84  tff(c_38, plain, (![A_51, B_52]: (k3_xboole_0(A_51, k9_relat_1(B_52, k1_relat_1(B_52)))=k9_relat_1(B_52, k10_relat_1(B_52, A_51)) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.60/3.84  tff(c_15006, plain, (![A_51]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_51))=k3_xboole_0(A_51, k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14741, c_38])).
% 9.60/3.84  tff(c_15034, plain, (![A_51]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_51))=k3_xboole_0(A_51, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_15006])).
% 9.60/3.84  tff(c_44, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.60/3.84  tff(c_70, plain, (k2_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_60])).
% 9.60/3.84  tff(c_562, plain, (![A_100, C_101, B_102]: (r1_tarski(k2_xboole_0(A_100, C_101), k2_xboole_0(B_102, C_101)) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.60/3.84  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.60/3.84  tff(c_683, plain, (![A_105, B_106, C_107]: (r1_tarski(A_105, k2_xboole_0(B_106, C_107)) | ~r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_562, c_10])).
% 9.60/3.84  tff(c_709, plain, (![A_105]: (r1_tarski(A_105, k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_105, k10_relat_1('#skF_3', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_683])).
% 9.60/3.84  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.60/3.84  tff(c_11344, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))='#skF_1'), inference(resolution, [status(thm)], [c_11324, c_14])).
% 9.60/3.84  tff(c_11351, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11344, c_38])).
% 9.60/3.84  tff(c_11361, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_11351])).
% 9.60/3.84  tff(c_34, plain, (![C_48, A_46, B_47]: (r1_tarski(k9_relat_1(C_48, A_46), k9_relat_1(C_48, B_47)) | ~r1_tarski(A_46, B_47) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.60/3.84  tff(c_11434, plain, (![B_47]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_47)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_47) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11361, c_34])).
% 9.60/3.84  tff(c_22175, plain, (![B_515]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_515)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_515))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_11434])).
% 9.60/3.84  tff(c_22248, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_709, c_22175])).
% 9.60/3.84  tff(c_22339, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_15034, c_22248])).
% 9.60/3.84  tff(c_15047, plain, (![A_419]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_419))=k3_xboole_0(A_419, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_15006])).
% 9.60/3.84  tff(c_1407, plain, (![B_135, A_136]: (r1_tarski(k9_relat_1(B_135, k10_relat_1(B_135, A_136)), A_136) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.60/3.84  tff(c_1418, plain, (![B_135, A_136]: (k2_xboole_0(k9_relat_1(B_135, k10_relat_1(B_135, A_136)), A_136)=A_136 | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_1407, c_12])).
% 9.60/3.84  tff(c_15080, plain, (![A_419]: (k2_xboole_0(k3_xboole_0(A_419, k2_relat_1('#skF_3')), A_419)=A_419 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15047, c_1418])).
% 9.60/3.84  tff(c_15365, plain, (![A_423]: (k2_xboole_0(k3_xboole_0(A_423, k2_relat_1('#skF_3')), A_423)=A_423)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_15080])).
% 9.60/3.84  tff(c_603, plain, (![A_100, B_102, C_101]: (r1_tarski(A_100, k2_xboole_0(B_102, C_101)) | ~r1_tarski(A_100, B_102))), inference(resolution, [status(thm)], [c_562, c_10])).
% 9.60/3.84  tff(c_15774, plain, (![A_100, A_423]: (r1_tarski(A_100, A_423) | ~r1_tarski(A_100, k3_xboole_0(A_423, k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_15365, c_603])).
% 9.60/3.84  tff(c_22365, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22339, c_15774])).
% 9.60/3.84  tff(c_22386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_22365])).
% 9.60/3.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.60/3.84  
% 9.60/3.84  Inference rules
% 9.60/3.84  ----------------------
% 9.60/3.84  #Ref     : 0
% 9.60/3.84  #Sup     : 5279
% 9.60/3.84  #Fact    : 0
% 9.60/3.84  #Define  : 0
% 9.60/3.84  #Split   : 5
% 9.60/3.84  #Chain   : 0
% 9.60/3.84  #Close   : 0
% 9.60/3.84  
% 9.60/3.84  Ordering : KBO
% 9.60/3.84  
% 9.60/3.84  Simplification rules
% 9.60/3.84  ----------------------
% 9.60/3.84  #Subsume      : 802
% 9.60/3.84  #Demod        : 2143
% 9.60/3.84  #Tautology    : 2378
% 9.60/3.84  #SimpNegUnit  : 2
% 9.60/3.84  #BackRed      : 8
% 9.60/3.84  
% 9.60/3.84  #Partial instantiations: 0
% 9.60/3.84  #Strategies tried      : 1
% 9.60/3.84  
% 9.60/3.84  Timing (in seconds)
% 9.60/3.84  ----------------------
% 9.60/3.84  Preprocessing        : 0.33
% 9.60/3.84  Parsing              : 0.18
% 9.60/3.84  CNF conversion       : 0.02
% 9.60/3.84  Main loop            : 2.75
% 9.60/3.84  Inferencing          : 0.61
% 9.60/3.84  Reduction            : 1.13
% 9.60/3.84  Demodulation         : 0.93
% 9.60/3.84  BG Simplification    : 0.08
% 9.60/3.85  Subsumption          : 0.78
% 9.60/3.85  Abstraction          : 0.10
% 9.60/3.85  MUC search           : 0.00
% 9.60/3.85  Cooper               : 0.00
% 9.60/3.85  Total                : 3.12
% 9.60/3.85  Index Insertion      : 0.00
% 9.60/3.85  Index Deletion       : 0.00
% 9.60/3.85  Index Matching       : 0.00
% 9.60/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
