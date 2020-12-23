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
% DateTime   : Thu Dec  3 10:14:53 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 154 expanded)
%              Number of leaves         :   39 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 309 expanded)
%              Number of equality atoms :   32 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_99,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_99])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_238,plain,(
    ! [B_113,A_114] :
      ( k1_tarski(k1_funct_1(B_113,A_114)) = k2_relat_1(B_113)
      | k1_tarski(A_114) != k1_relat_1(B_113)
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_195,plain,(
    ! [D_99] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_99) = k9_relat_1('#skF_4',D_99) ),
    inference(resolution,[status(thm)],[c_54,c_189])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_197,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_50])).

tff(c_244,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_197])).

tff(c_250,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_58,c_244])).

tff(c_252,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_146,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_154,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_804,plain,(
    ! [B_208,A_209,C_210] :
      ( k1_xboole_0 = B_208
      | k1_relset_1(A_209,B_208,C_210) = A_209
      | ~ v1_funct_2(C_210,A_209,B_208)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_817,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_804])).

tff(c_827,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_154,c_817])).

tff(c_829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_52,c_827])).

tff(c_831,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_836,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_54])).

tff(c_1095,plain,(
    ! [D_258,C_259,B_260,A_261] :
      ( m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(C_259,B_260)))
      | ~ r1_tarski(k2_relat_1(D_258),B_260)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(C_259,A_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1107,plain,(
    ! [B_262] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_262)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_262) ) ),
    inference(resolution,[status(thm)],[c_836,c_1095])).

tff(c_34,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k7_relset_1(A_45,B_46,C_47,D_48) = k9_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1211,plain,(
    ! [B_267,D_268] :
      ( k7_relset_1(k1_relat_1('#skF_4'),B_267,'#skF_4',D_268) = k9_relat_1('#skF_4',D_268)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_267) ) ),
    inference(resolution,[status(thm)],[c_1107,c_34])).

tff(c_1225,plain,(
    ! [D_276] : k7_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4',D_276) = k9_relat_1('#skF_4',D_276) ),
    inference(resolution,[status(thm)],[c_6,c_1211])).

tff(c_879,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( m1_subset_1(k7_relset_1(A_211,B_212,C_213,D_214),k1_zfmisc_1(B_212))
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_905,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( r1_tarski(k7_relset_1(A_211,B_212,C_213,D_214),B_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(resolution,[status(thm)],[c_879,c_22])).

tff(c_1128,plain,(
    ! [B_262,D_214] :
      ( r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),B_262,'#skF_4',D_214),B_262)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_262) ) ),
    inference(resolution,[status(thm)],[c_1107,c_905])).

tff(c_1231,plain,(
    ! [D_276] :
      ( r1_tarski(k9_relat_1('#skF_4',D_276),k2_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_1128])).

tff(c_1243,plain,(
    ! [D_276] : r1_tarski(k9_relat_1('#skF_4',D_276),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1231])).

tff(c_830,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_1247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_830])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.66  
% 3.61/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.66  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.61/1.66  
% 3.61/1.66  %Foreground sorts:
% 3.61/1.66  
% 3.61/1.66  
% 3.61/1.66  %Background operators:
% 3.61/1.66  
% 3.61/1.66  
% 3.61/1.66  %Foreground operators:
% 3.61/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.61/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.61/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.61/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.61/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.61/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.61/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.61/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.61/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.66  
% 3.61/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.61/1.67  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.61/1.67  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.61/1.67  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.61/1.67  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.61/1.67  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.61/1.67  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.61/1.67  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 3.61/1.67  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.61/1.67  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.61/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.67  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.61/1.67  tff(c_99, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.61/1.67  tff(c_107, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_99])).
% 3.61/1.67  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.61/1.67  tff(c_238, plain, (![B_113, A_114]: (k1_tarski(k1_funct_1(B_113, A_114))=k2_relat_1(B_113) | k1_tarski(A_114)!=k1_relat_1(B_113) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.61/1.67  tff(c_189, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.61/1.67  tff(c_195, plain, (![D_99]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_99)=k9_relat_1('#skF_4', D_99))), inference(resolution, [status(thm)], [c_54, c_189])).
% 3.61/1.67  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.61/1.67  tff(c_197, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_50])).
% 3.61/1.67  tff(c_244, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_238, c_197])).
% 3.61/1.67  tff(c_250, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_58, c_244])).
% 3.61/1.67  tff(c_252, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_250])).
% 3.61/1.67  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.61/1.67  tff(c_56, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.61/1.67  tff(c_146, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.61/1.67  tff(c_154, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_146])).
% 3.61/1.67  tff(c_804, plain, (![B_208, A_209, C_210]: (k1_xboole_0=B_208 | k1_relset_1(A_209, B_208, C_210)=A_209 | ~v1_funct_2(C_210, A_209, B_208) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.61/1.67  tff(c_817, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_54, c_804])).
% 3.61/1.67  tff(c_827, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_154, c_817])).
% 3.61/1.67  tff(c_829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_52, c_827])).
% 3.61/1.67  tff(c_831, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_250])).
% 3.61/1.67  tff(c_836, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_831, c_54])).
% 3.61/1.67  tff(c_1095, plain, (![D_258, C_259, B_260, A_261]: (m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(C_259, B_260))) | ~r1_tarski(k2_relat_1(D_258), B_260) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(C_259, A_261))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.61/1.67  tff(c_1107, plain, (![B_262]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_262))) | ~r1_tarski(k2_relat_1('#skF_4'), B_262))), inference(resolution, [status(thm)], [c_836, c_1095])).
% 3.61/1.67  tff(c_34, plain, (![A_45, B_46, C_47, D_48]: (k7_relset_1(A_45, B_46, C_47, D_48)=k9_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.61/1.67  tff(c_1211, plain, (![B_267, D_268]: (k7_relset_1(k1_relat_1('#skF_4'), B_267, '#skF_4', D_268)=k9_relat_1('#skF_4', D_268) | ~r1_tarski(k2_relat_1('#skF_4'), B_267))), inference(resolution, [status(thm)], [c_1107, c_34])).
% 3.61/1.67  tff(c_1225, plain, (![D_276]: (k7_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', D_276)=k9_relat_1('#skF_4', D_276))), inference(resolution, [status(thm)], [c_6, c_1211])).
% 3.61/1.67  tff(c_879, plain, (![A_211, B_212, C_213, D_214]: (m1_subset_1(k7_relset_1(A_211, B_212, C_213, D_214), k1_zfmisc_1(B_212)) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.61/1.67  tff(c_22, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.61/1.67  tff(c_905, plain, (![A_211, B_212, C_213, D_214]: (r1_tarski(k7_relset_1(A_211, B_212, C_213, D_214), B_212) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(resolution, [status(thm)], [c_879, c_22])).
% 3.61/1.67  tff(c_1128, plain, (![B_262, D_214]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), B_262, '#skF_4', D_214), B_262) | ~r1_tarski(k2_relat_1('#skF_4'), B_262))), inference(resolution, [status(thm)], [c_1107, c_905])).
% 3.61/1.67  tff(c_1231, plain, (![D_276]: (r1_tarski(k9_relat_1('#skF_4', D_276), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1225, c_1128])).
% 3.61/1.67  tff(c_1243, plain, (![D_276]: (r1_tarski(k9_relat_1('#skF_4', D_276), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1231])).
% 3.61/1.67  tff(c_830, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_250])).
% 3.61/1.67  tff(c_1247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1243, c_830])).
% 3.61/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.67  
% 3.61/1.67  Inference rules
% 3.61/1.67  ----------------------
% 3.61/1.67  #Ref     : 0
% 3.61/1.67  #Sup     : 256
% 3.61/1.67  #Fact    : 0
% 3.61/1.67  #Define  : 0
% 3.61/1.67  #Split   : 4
% 3.61/1.67  #Chain   : 0
% 3.61/1.67  #Close   : 0
% 3.61/1.67  
% 3.61/1.67  Ordering : KBO
% 3.61/1.67  
% 3.61/1.67  Simplification rules
% 3.61/1.67  ----------------------
% 3.61/1.67  #Subsume      : 13
% 3.61/1.67  #Demod        : 59
% 3.61/1.67  #Tautology    : 77
% 3.61/1.67  #SimpNegUnit  : 2
% 3.61/1.67  #BackRed      : 8
% 3.61/1.67  
% 3.61/1.67  #Partial instantiations: 0
% 3.61/1.67  #Strategies tried      : 1
% 3.61/1.67  
% 3.61/1.67  Timing (in seconds)
% 3.61/1.67  ----------------------
% 3.61/1.68  Preprocessing        : 0.39
% 3.61/1.68  Parsing              : 0.21
% 3.61/1.68  CNF conversion       : 0.03
% 3.61/1.68  Main loop            : 0.47
% 3.61/1.68  Inferencing          : 0.18
% 3.61/1.68  Reduction            : 0.14
% 3.61/1.68  Demodulation         : 0.10
% 3.61/1.68  BG Simplification    : 0.03
% 3.61/1.68  Subsumption          : 0.09
% 3.61/1.68  Abstraction          : 0.03
% 3.61/1.68  MUC search           : 0.00
% 3.61/1.68  Cooper               : 0.00
% 3.61/1.68  Total                : 0.89
% 3.61/1.68  Index Insertion      : 0.00
% 3.61/1.68  Index Deletion       : 0.00
% 3.61/1.68  Index Matching       : 0.00
% 3.61/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
