%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:45 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 177 expanded)
%              Number of leaves         :   38 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 349 expanded)
%              Number of equality atoms :   42 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_18,c_79])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_125,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_137,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_125])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,A_16),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = k1_xboole_0
      | k2_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_143,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_32])).

tff(c_148,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_319,plain,(
    ! [A_80] :
      ( k2_relat_1(A_80) = k1_xboole_0
      | k1_relat_1(A_80) != k1_xboole_0
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_325,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_319])).

tff(c_329,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_325])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_589,plain,(
    ! [B_120,A_121] :
      ( k1_tarski(k1_funct_1(B_120,A_121)) = k2_relat_1(B_120)
      | k1_tarski(A_121) != k1_relat_1(B_120)
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_598,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_46])).

tff(c_604,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_54,c_598])).

tff(c_609,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_604])).

tff(c_503,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_515,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_503])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_485,plain,(
    ! [B_104,A_105] :
      ( k1_tarski(B_104) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_tarski(B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_988,plain,(
    ! [B_197,B_198] :
      ( k1_tarski(B_197) = k1_relat_1(B_198)
      | k1_relat_1(B_198) = k1_xboole_0
      | ~ v4_relat_1(B_198,k1_tarski(B_197))
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_28,c_485])).

tff(c_1018,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_515,c_988])).

tff(c_1043,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1018])).

tff(c_1045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_609,c_1043])).

tff(c_1047,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_604])).

tff(c_1053,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_50])).

tff(c_1106,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( k7_relset_1(A_200,B_201,C_202,D_203) = k9_relat_1(C_202,D_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1115,plain,(
    ! [D_203] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_203) = k9_relat_1('#skF_4',D_203) ),
    inference(resolution,[status(thm)],[c_1053,c_1106])).

tff(c_1046,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_604])).

tff(c_1104,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1047,c_1046])).

tff(c_1154,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1104])).

tff(c_1166,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1154])).

tff(c_1170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1166])).

tff(c_1172,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_1180,plain,(
    ! [A_16] :
      ( r1_tarski(k9_relat_1('#skF_4',A_16),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_30])).

tff(c_1186,plain,(
    ! [A_209] : r1_tarski(k9_relat_1('#skF_4',A_209),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1180])).

tff(c_95,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_91,c_95])).

tff(c_1192,plain,(
    ! [A_209] : k9_relat_1('#skF_4',A_209) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1186,c_106])).

tff(c_1873,plain,(
    ! [A_317,B_318,C_319,D_320] :
      ( k7_relset_1(A_317,B_318,C_319,D_320) = k9_relat_1(C_319,D_320)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1875,plain,(
    ! [D_320] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_320) = k9_relat_1('#skF_4',D_320) ),
    inference(resolution,[status(thm)],[c_50,c_1873])).

tff(c_1883,plain,(
    ! [D_320] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_320) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_1875])).

tff(c_1894,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_46])).

tff(c_1897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.58  
% 3.46/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.58  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.46/1.58  
% 3.46/1.58  %Foreground sorts:
% 3.46/1.58  
% 3.46/1.58  
% 3.46/1.58  %Background operators:
% 3.46/1.58  
% 3.46/1.58  
% 3.46/1.58  %Foreground operators:
% 3.46/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.58  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.46/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.46/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.46/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.46/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.46/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.46/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.58  
% 3.46/1.60  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.46/1.60  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.46/1.60  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.46/1.60  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.46/1.60  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.46/1.60  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.46/1.60  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.46/1.60  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.46/1.60  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.46/1.60  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.46/1.60  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.46/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.60  tff(c_18, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.60  tff(c_79, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.60  tff(c_91, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_18, c_79])).
% 3.46/1.60  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.46/1.60  tff(c_125, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.46/1.60  tff(c_137, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_125])).
% 3.46/1.60  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, A_16), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.60  tff(c_32, plain, (![A_18]: (k1_relat_1(A_18)=k1_xboole_0 | k2_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.46/1.60  tff(c_143, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_32])).
% 3.46/1.60  tff(c_148, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_143])).
% 3.46/1.60  tff(c_319, plain, (![A_80]: (k2_relat_1(A_80)=k1_xboole_0 | k1_relat_1(A_80)!=k1_xboole_0 | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.46/1.60  tff(c_325, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_319])).
% 3.46/1.60  tff(c_329, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_148, c_325])).
% 3.46/1.60  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.46/1.60  tff(c_589, plain, (![B_120, A_121]: (k1_tarski(k1_funct_1(B_120, A_121))=k2_relat_1(B_120) | k1_tarski(A_121)!=k1_relat_1(B_120) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.46/1.60  tff(c_46, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.46/1.60  tff(c_598, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_589, c_46])).
% 3.46/1.60  tff(c_604, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_54, c_598])).
% 3.46/1.60  tff(c_609, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_604])).
% 3.46/1.60  tff(c_503, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.60  tff(c_515, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_503])).
% 3.46/1.60  tff(c_28, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.60  tff(c_485, plain, (![B_104, A_105]: (k1_tarski(B_104)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_tarski(B_104)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.60  tff(c_988, plain, (![B_197, B_198]: (k1_tarski(B_197)=k1_relat_1(B_198) | k1_relat_1(B_198)=k1_xboole_0 | ~v4_relat_1(B_198, k1_tarski(B_197)) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_28, c_485])).
% 3.46/1.60  tff(c_1018, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_515, c_988])).
% 3.46/1.60  tff(c_1043, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1018])).
% 3.46/1.60  tff(c_1045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_329, c_609, c_1043])).
% 3.46/1.60  tff(c_1047, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_604])).
% 3.46/1.60  tff(c_1053, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_50])).
% 3.46/1.60  tff(c_1106, plain, (![A_200, B_201, C_202, D_203]: (k7_relset_1(A_200, B_201, C_202, D_203)=k9_relat_1(C_202, D_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.46/1.60  tff(c_1115, plain, (![D_203]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_203)=k9_relat_1('#skF_4', D_203))), inference(resolution, [status(thm)], [c_1053, c_1106])).
% 3.46/1.60  tff(c_1046, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_604])).
% 3.46/1.60  tff(c_1104, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1047, c_1046])).
% 3.46/1.60  tff(c_1154, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1104])).
% 3.46/1.60  tff(c_1166, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1154])).
% 3.46/1.60  tff(c_1170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_1166])).
% 3.46/1.60  tff(c_1172, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_143])).
% 3.46/1.60  tff(c_1180, plain, (![A_16]: (r1_tarski(k9_relat_1('#skF_4', A_16), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1172, c_30])).
% 3.46/1.60  tff(c_1186, plain, (![A_209]: (r1_tarski(k9_relat_1('#skF_4', A_209), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1180])).
% 3.46/1.60  tff(c_95, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.60  tff(c_106, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_91, c_95])).
% 3.46/1.60  tff(c_1192, plain, (![A_209]: (k9_relat_1('#skF_4', A_209)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1186, c_106])).
% 3.46/1.60  tff(c_1873, plain, (![A_317, B_318, C_319, D_320]: (k7_relset_1(A_317, B_318, C_319, D_320)=k9_relat_1(C_319, D_320) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.46/1.60  tff(c_1875, plain, (![D_320]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_320)=k9_relat_1('#skF_4', D_320))), inference(resolution, [status(thm)], [c_50, c_1873])).
% 3.46/1.60  tff(c_1883, plain, (![D_320]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_320)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_1875])).
% 3.46/1.60  tff(c_1894, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_46])).
% 3.46/1.60  tff(c_1897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_1894])).
% 3.46/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.60  
% 3.46/1.60  Inference rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Ref     : 0
% 3.46/1.60  #Sup     : 343
% 3.46/1.60  #Fact    : 0
% 3.46/1.60  #Define  : 0
% 3.46/1.60  #Split   : 9
% 3.46/1.60  #Chain   : 0
% 3.46/1.60  #Close   : 0
% 3.46/1.60  
% 3.46/1.60  Ordering : KBO
% 3.46/1.60  
% 3.46/1.60  Simplification rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Subsume      : 8
% 3.46/1.60  #Demod        : 286
% 3.46/1.60  #Tautology    : 180
% 3.46/1.60  #SimpNegUnit  : 9
% 3.46/1.60  #BackRed      : 14
% 3.46/1.60  
% 3.46/1.60  #Partial instantiations: 0
% 3.46/1.60  #Strategies tried      : 1
% 3.46/1.60  
% 3.46/1.60  Timing (in seconds)
% 3.46/1.60  ----------------------
% 3.46/1.60  Preprocessing        : 0.33
% 3.46/1.60  Parsing              : 0.18
% 3.46/1.60  CNF conversion       : 0.02
% 3.46/1.60  Main loop            : 0.51
% 3.46/1.60  Inferencing          : 0.19
% 3.46/1.60  Reduction            : 0.17
% 3.46/1.60  Demodulation         : 0.12
% 3.46/1.60  BG Simplification    : 0.02
% 3.46/1.60  Subsumption          : 0.08
% 3.46/1.60  Abstraction          : 0.02
% 3.46/1.60  MUC search           : 0.00
% 3.46/1.60  Cooper               : 0.00
% 3.46/1.60  Total                : 0.87
% 3.46/1.60  Index Insertion      : 0.00
% 3.46/1.60  Index Deletion       : 0.00
% 3.46/1.60  Index Matching       : 0.00
% 3.46/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
