%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:06 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 424 expanded)
%              Number of leaves         :   28 ( 168 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 (1010 expanded)
%              Number of equality atoms :   36 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( k6_subset_1(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16)) = k9_relat_1(C_17,k6_subset_1(A_15,B_16))
      | ~ v2_funct_1(C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1225,plain,(
    ! [C_91,A_92,B_93] :
      ( k4_xboole_0(k9_relat_1(C_91,A_92),k9_relat_1(C_91,B_93)) = k9_relat_1(C_91,k4_xboole_0(A_92,B_93))
      | ~ v2_funct_1(C_91)
      | ~ v1_funct_1(C_91)
      | ~ v1_relat_1(C_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_34,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_111,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_1243,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_128])).

tff(c_1272,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1243])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,k9_relat_1(B_21,A_20)),A_20)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1287,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k4_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_26])).

tff(c_1298,plain,(
    r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1287])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_16,c_68])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(k2_xboole_0(A_42,B_44),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_258,plain,(
    ! [A_45,B_46] : r1_tarski(A_45,k2_xboole_0(A_45,B_46)) ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_404,plain,(
    ! [A_53,B_54,B_55] : r1_tarski(A_53,k2_xboole_0(k2_xboole_0(A_53,B_54),B_55)) ),
    inference(resolution,[status(thm)],[c_258,c_12])).

tff(c_502,plain,(
    ! [A_60,B_61,B_62] : r1_tarski(k4_xboole_0(A_60,B_61),k2_xboole_0(A_60,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_404])).

tff(c_516,plain,(
    ! [B_61] : r1_tarski(k4_xboole_0('#skF_1',B_61),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_502])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,k10_relat_1(B_19,k9_relat_1(B_19,A_18)))
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1290,plain,
    ( r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_24])).

tff(c_1300,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_516,c_1290])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1320,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k10_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1300,c_2])).

tff(c_1329,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k10_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_1320])).

tff(c_63,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_67,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_28])).

tff(c_1335,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_67])).

tff(c_129,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_1360,plain,(
    k4_xboole_0(k10_relat_1('#skF_3',k1_xboole_0),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_129])).

tff(c_288,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_307,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_16,c_288])).

tff(c_1503,plain,
    ( k4_xboole_0(k10_relat_1('#skF_3',k1_xboole_0),'#skF_1') = k10_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_307])).

tff(c_1530,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1503])).

tff(c_1531,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1335,c_1530])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_435,plain,(
    ! [A_53,B_54,B_55] : k4_xboole_0(A_53,k2_xboole_0(k2_xboole_0(A_53,B_54),B_55)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_404,c_10])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [C_17,A_15,B_16] :
      ( k4_xboole_0(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16)) = k9_relat_1(C_17,k4_xboole_0(A_15,B_16))
      | ~ v2_funct_1(C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_1281,plain,(
    ! [B_16] :
      ( k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_16)) = k4_xboole_0(k1_xboole_0,k9_relat_1('#skF_3',B_16))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_39])).

tff(c_1294,plain,(
    ! [B_16] : k9_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_16)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_18,c_1281])).

tff(c_1852,plain,(
    ! [B_105] : k9_relat_1('#skF_3',k4_xboole_0(k10_relat_1('#skF_3',k1_xboole_0),B_105)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1294])).

tff(c_1875,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_1852])).

tff(c_1901,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1875,c_26])).

tff(c_1912,plain,(
    r1_tarski(k10_relat_1('#skF_3',k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1901])).

tff(c_1914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1531,c_1912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n001.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:13:15 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.53  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.53  
% 3.31/1.53  %Foreground sorts:
% 3.31/1.53  
% 3.31/1.53  
% 3.31/1.53  %Background operators:
% 3.31/1.53  
% 3.31/1.53  
% 3.31/1.53  %Foreground operators:
% 3.31/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.31/1.53  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.31/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.31/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.53  
% 3.44/1.54  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.44/1.54  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.44/1.54  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 3.44/1.54  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.44/1.54  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 3.44/1.54  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.44/1.54  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.44/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.54  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.44/1.54  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.44/1.54  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.44/1.54  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_20, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.54  tff(c_22, plain, (![C_17, A_15, B_16]: (k6_subset_1(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16))=k9_relat_1(C_17, k6_subset_1(A_15, B_16)) | ~v2_funct_1(C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.54  tff(c_1225, plain, (![C_91, A_92, B_93]: (k4_xboole_0(k9_relat_1(C_91, A_92), k9_relat_1(C_91, B_93))=k9_relat_1(C_91, k4_xboole_0(A_92, B_93)) | ~v2_funct_1(C_91) | ~v1_funct_1(C_91) | ~v1_relat_1(C_91))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.44/1.54  tff(c_34, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_111, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.54  tff(c_128, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_111])).
% 3.44/1.54  tff(c_1243, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1225, c_128])).
% 3.44/1.54  tff(c_1272, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1243])).
% 3.44/1.54  tff(c_26, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, k9_relat_1(B_21, A_20)), A_20) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.44/1.54  tff(c_1287, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1272, c_26])).
% 3.44/1.54  tff(c_1298, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1287])).
% 3.44/1.54  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_68, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.54  tff(c_87, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_68])).
% 3.44/1.54  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.54  tff(c_86, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_16, c_68])).
% 3.44/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.54  tff(c_234, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(k2_xboole_0(A_42, B_44), C_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.54  tff(c_258, plain, (![A_45, B_46]: (r1_tarski(A_45, k2_xboole_0(A_45, B_46)))), inference(resolution, [status(thm)], [c_6, c_234])).
% 3.44/1.54  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.54  tff(c_404, plain, (![A_53, B_54, B_55]: (r1_tarski(A_53, k2_xboole_0(k2_xboole_0(A_53, B_54), B_55)))), inference(resolution, [status(thm)], [c_258, c_12])).
% 3.44/1.54  tff(c_502, plain, (![A_60, B_61, B_62]: (r1_tarski(k4_xboole_0(A_60, B_61), k2_xboole_0(A_60, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_404])).
% 3.44/1.54  tff(c_516, plain, (![B_61]: (r1_tarski(k4_xboole_0('#skF_1', B_61), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_87, c_502])).
% 3.44/1.54  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(A_18, k10_relat_1(B_19, k9_relat_1(B_19, A_18))) | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.54  tff(c_1290, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0)) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1272, c_24])).
% 3.44/1.54  tff(c_1300, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_516, c_1290])).
% 3.44/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.54  tff(c_1320, plain, (k4_xboole_0('#skF_1', '#skF_2')=k10_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1300, c_2])).
% 3.44/1.54  tff(c_1329, plain, (k4_xboole_0('#skF_1', '#skF_2')=k10_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_1320])).
% 3.44/1.54  tff(c_63, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.54  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_67, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_28])).
% 3.44/1.54  tff(c_1335, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_67])).
% 3.44/1.54  tff(c_129, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_111])).
% 3.44/1.54  tff(c_1360, plain, (k4_xboole_0(k10_relat_1('#skF_3', k1_xboole_0), '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1329, c_129])).
% 3.44/1.54  tff(c_288, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.54  tff(c_307, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_16, c_288])).
% 3.44/1.54  tff(c_1503, plain, (k4_xboole_0(k10_relat_1('#skF_3', k1_xboole_0), '#skF_1')=k10_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1360, c_307])).
% 3.44/1.54  tff(c_1530, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1503])).
% 3.44/1.54  tff(c_1531, plain, (~r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1335, c_1530])).
% 3.44/1.54  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.54  tff(c_435, plain, (![A_53, B_54, B_55]: (k4_xboole_0(A_53, k2_xboole_0(k2_xboole_0(A_53, B_54), B_55))=k1_xboole_0)), inference(resolution, [status(thm)], [c_404, c_10])).
% 3.44/1.54  tff(c_18, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.54  tff(c_39, plain, (![C_17, A_15, B_16]: (k4_xboole_0(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16))=k9_relat_1(C_17, k4_xboole_0(A_15, B_16)) | ~v2_funct_1(C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.44/1.54  tff(c_1281, plain, (![B_16]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_16))=k4_xboole_0(k1_xboole_0, k9_relat_1('#skF_3', B_16)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1272, c_39])).
% 3.44/1.54  tff(c_1294, plain, (![B_16]: (k9_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_16))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_18, c_1281])).
% 3.44/1.54  tff(c_1852, plain, (![B_105]: (k9_relat_1('#skF_3', k4_xboole_0(k10_relat_1('#skF_3', k1_xboole_0), B_105))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1294])).
% 3.44/1.54  tff(c_1875, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_435, c_1852])).
% 3.44/1.54  tff(c_1901, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1875, c_26])).
% 3.44/1.54  tff(c_1912, plain, (r1_tarski(k10_relat_1('#skF_3', k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1901])).
% 3.44/1.54  tff(c_1914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1531, c_1912])).
% 3.44/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.54  
% 3.44/1.54  Inference rules
% 3.44/1.54  ----------------------
% 3.44/1.54  #Ref     : 0
% 3.44/1.54  #Sup     : 462
% 3.44/1.54  #Fact    : 0
% 3.44/1.54  #Define  : 0
% 3.44/1.54  #Split   : 2
% 3.44/1.54  #Chain   : 0
% 3.44/1.54  #Close   : 0
% 3.44/1.54  
% 3.44/1.54  Ordering : KBO
% 3.44/1.54  
% 3.44/1.54  Simplification rules
% 3.44/1.54  ----------------------
% 3.44/1.54  #Subsume      : 17
% 3.44/1.54  #Demod        : 319
% 3.44/1.54  #Tautology    : 274
% 3.44/1.54  #SimpNegUnit  : 3
% 3.44/1.54  #BackRed      : 4
% 3.44/1.54  
% 3.44/1.54  #Partial instantiations: 0
% 3.44/1.54  #Strategies tried      : 1
% 3.44/1.54  
% 3.44/1.54  Timing (in seconds)
% 3.44/1.54  ----------------------
% 3.44/1.55  Preprocessing        : 0.29
% 3.44/1.55  Parsing              : 0.15
% 3.44/1.55  CNF conversion       : 0.02
% 3.44/1.55  Main loop            : 0.48
% 3.44/1.55  Inferencing          : 0.16
% 3.44/1.55  Reduction            : 0.18
% 3.44/1.55  Demodulation         : 0.14
% 3.44/1.55  BG Simplification    : 0.02
% 3.44/1.55  Subsumption          : 0.09
% 3.44/1.55  Abstraction          : 0.03
% 3.44/1.55  MUC search           : 0.00
% 3.44/1.55  Cooper               : 0.00
% 3.44/1.55  Total                : 0.80
% 3.44/1.55  Index Insertion      : 0.00
% 3.44/1.55  Index Deletion       : 0.00
% 3.44/1.55  Index Matching       : 0.00
% 3.44/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
