%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:59 EST 2020

% Result     : Theorem 8.35s
% Output     : CNFRefutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 537 expanded)
%              Number of leaves         :   56 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          :  214 (1132 expanded)
%              Number of equality atoms :   61 ( 247 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_139,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_54,plain,(
    ! [A_50,B_51] : v1_relat_1(k2_zfmisc_1(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_314,plain,(
    ! [B_104,A_105] :
      ( v1_relat_1(B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_105))
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_317,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_314])).

tff(c_323,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_317])).

tff(c_70,plain,(
    ! [B_61,A_60] :
      ( r1_tarski(k7_relat_1(B_61,A_60),B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_400,plain,(
    ! [A_114,B_115] :
      ( v1_relat_1(A_114)
      | ~ v1_relat_1(B_115)
      | ~ r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_46,c_314])).

tff(c_419,plain,(
    ! [B_61,A_60] :
      ( v1_relat_1(k7_relat_1(B_61,A_60))
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_70,c_400])).

tff(c_56,plain,(
    ! [B_53,A_52] :
      ( k2_relat_1(k7_relat_1(B_53,A_52)) = k9_relat_1(B_53,A_52)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1027,plain,(
    ! [A_182,B_183] :
      ( r1_tarski(k2_relat_1(A_182),k2_relat_1(B_183))
      | ~ r1_tarski(A_182,B_183)
      | ~ v1_relat_1(B_183)
      | ~ v1_relat_1(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10793,plain,(
    ! [B_650,A_651,B_652] :
      ( r1_tarski(k9_relat_1(B_650,A_651),k2_relat_1(B_652))
      | ~ r1_tarski(k7_relat_1(B_650,A_651),B_652)
      | ~ v1_relat_1(B_652)
      | ~ v1_relat_1(k7_relat_1(B_650,A_651))
      | ~ v1_relat_1(B_650) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1027])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_38,plain,(
    ! [B_40] : k2_zfmisc_1(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1192,plain,(
    ! [B_199,A_200] :
      ( k1_tarski(k1_funct_1(B_199,A_200)) = k2_relat_1(B_199)
      | k1_tarski(A_200) != k1_relat_1(B_199)
      | ~ v1_funct_1(B_199)
      | ~ v1_relat_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_80,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1211,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_80])).

tff(c_1229,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_88,c_1211])).

tff(c_1286,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1229])).

tff(c_597,plain,(
    ! [C_149,A_150,B_151] :
      ( v4_relat_1(C_149,A_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_611,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_597])).

tff(c_14,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_540,plain,(
    ! [B_142,A_143] :
      ( r1_tarski(k1_relat_1(B_142),A_143)
      | ~ v4_relat_1(B_142,A_143)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1624,plain,(
    ! [B_234,A_235] :
      ( k3_xboole_0(k1_relat_1(B_234),A_235) = k1_relat_1(B_234)
      | ~ v4_relat_1(B_234,A_235)
      | ~ v1_relat_1(B_234) ) ),
    inference(resolution,[status(thm)],[c_540,c_10])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1634,plain,(
    ! [B_234,A_235] :
      ( k5_xboole_0(k1_relat_1(B_234),k1_relat_1(B_234)) = k4_xboole_0(k1_relat_1(B_234),A_235)
      | ~ v4_relat_1(B_234,A_235)
      | ~ v1_relat_1(B_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_8])).

tff(c_1662,plain,(
    ! [B_236,A_237] :
      ( k4_xboole_0(k1_relat_1(B_236),A_237) = k1_xboole_0
      | ~ v4_relat_1(B_236,A_237)
      | ~ v1_relat_1(B_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1634])).

tff(c_40,plain,(
    ! [B_42,A_41] :
      ( ~ r2_hidden(B_42,A_41)
      | k4_xboole_0(A_41,k1_tarski(B_42)) != A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3232,plain,(
    ! [B_337,B_338] :
      ( ~ r2_hidden(B_337,k1_relat_1(B_338))
      | k1_relat_1(B_338) != k1_xboole_0
      | ~ v4_relat_1(B_338,k1_tarski(B_337))
      | ~ v1_relat_1(B_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1662,c_40])).

tff(c_3266,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_4'))
    | k1_relat_1('#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_611,c_3232])).

tff(c_3282,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_4'))
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_3266])).

tff(c_3286,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3282])).

tff(c_42,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,k1_tarski(B_42)) = A_41
      | r2_hidden(B_42,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3299,plain,(
    ! [B_341,B_342] :
      ( k1_relat_1(B_341) = k1_xboole_0
      | ~ v4_relat_1(B_341,k1_tarski(B_342))
      | ~ v1_relat_1(B_341)
      | r2_hidden(B_342,k1_relat_1(B_341)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1662])).

tff(c_3333,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_611,c_3299])).

tff(c_3349,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_3333])).

tff(c_3350,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_3286,c_3349])).

tff(c_52,plain,(
    ! [B_49,A_48] :
      ( r1_tarski(k1_relat_1(B_49),A_48)
      | ~ v4_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_343,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(B_110,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1287,plain,(
    ! [A_208,B_209] :
      ( k1_tarski(A_208) = B_209
      | ~ r1_tarski(B_209,k1_tarski(A_208))
      | ~ r2_hidden(A_208,B_209) ) ),
    inference(resolution,[status(thm)],[c_32,c_343])).

tff(c_3771,plain,(
    ! [A_361,B_362] :
      ( k1_tarski(A_361) = k1_relat_1(B_362)
      | ~ r2_hidden(A_361,k1_relat_1(B_362))
      | ~ v4_relat_1(B_362,k1_tarski(A_361))
      | ~ v1_relat_1(B_362) ) ),
    inference(resolution,[status(thm)],[c_52,c_1287])).

tff(c_3805,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_611,c_3771])).

tff(c_3821,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_3350,c_3805])).

tff(c_3823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1286,c_3821])).

tff(c_3825,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3282])).

tff(c_60,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,k2_zfmisc_1(k1_relat_1(A_56),k2_relat_1(A_56)))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3913,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3825,c_60])).

tff(c_3982,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_38,c_3913])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_361,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_343])).

tff(c_4045,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3982,c_361])).

tff(c_4113,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4045,c_12])).

tff(c_129,plain,(
    ! [A_76,B_77] : v1_relat_1(k2_zfmisc_1(A_76,B_77)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_131,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_129])).

tff(c_66,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_362,plain,(
    ! [A_112] :
      ( k1_xboole_0 = A_112
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_343])).

tff(c_366,plain,(
    ! [A_60] :
      ( k7_relat_1(k1_xboole_0,A_60) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_70,c_362])).

tff(c_381,plain,(
    ! [A_60] : k7_relat_1(k1_xboole_0,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_366])).

tff(c_434,plain,(
    ! [B_120,A_121] :
      ( k2_relat_1(k7_relat_1(B_120,A_121)) = k9_relat_1(B_120,A_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_443,plain,(
    ! [A_60] :
      ( k9_relat_1(k1_xboole_0,A_60) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_434])).

tff(c_447,plain,(
    ! [A_60] : k9_relat_1(k1_xboole_0,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_66,c_443])).

tff(c_4097,plain,(
    ! [A_60] : k9_relat_1('#skF_4',A_60) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4045,c_4045,c_447])).

tff(c_1442,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k7_relset_1(A_215,B_216,C_217,D_218) = k9_relat_1(C_217,D_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1452,plain,(
    ! [D_218] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_218) = k9_relat_1('#skF_4',D_218) ),
    inference(resolution,[status(thm)],[c_84,c_1442])).

tff(c_1454,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_80])).

tff(c_4893,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4097,c_1454])).

tff(c_4897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4113,c_4893])).

tff(c_4899,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1229])).

tff(c_72,plain,(
    ! [B_63,A_62] :
      ( k1_tarski(k1_funct_1(B_63,A_62)) = k2_relat_1(B_63)
      | k1_tarski(A_62) != k1_relat_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4908,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4899,c_84])).

tff(c_78,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k7_relset_1(A_67,B_68,C_69,D_70) = k9_relat_1(C_69,D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5028,plain,(
    ! [D_70] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_70) = k9_relat_1('#skF_4',D_70) ),
    inference(resolution,[status(thm)],[c_4908,c_78])).

tff(c_4905,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4899,c_80])).

tff(c_5283,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5028,c_4905])).

tff(c_5295,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_5283])).

tff(c_5297,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_88,c_4899,c_5295])).

tff(c_10800,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10793,c_5297])).

tff(c_10849,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_10800])).

tff(c_10865,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10849])).

tff(c_10868,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_419,c_10865])).

tff(c_10872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_10868])).

tff(c_10873,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_10849])).

tff(c_10882,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_10873])).

tff(c_10886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_10882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.35/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.84  
% 8.35/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.35/2.85  
% 8.35/2.85  %Foreground sorts:
% 8.35/2.85  
% 8.35/2.85  
% 8.35/2.85  %Background operators:
% 8.35/2.85  
% 8.35/2.85  
% 8.35/2.85  %Foreground operators:
% 8.35/2.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.35/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.35/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.35/2.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.35/2.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.35/2.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.35/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.35/2.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.35/2.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.35/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.35/2.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.35/2.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.35/2.85  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.35/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.35/2.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.35/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.35/2.85  tff('#skF_2', type, '#skF_2': $i).
% 8.35/2.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.35/2.85  tff('#skF_3', type, '#skF_3': $i).
% 8.35/2.85  tff('#skF_1', type, '#skF_1': $i).
% 8.35/2.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.35/2.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.35/2.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.35/2.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.35/2.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.35/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.35/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.35/2.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.35/2.85  tff('#skF_4', type, '#skF_4': $i).
% 8.35/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.35/2.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.35/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.35/2.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.35/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.35/2.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.35/2.85  
% 8.35/2.86  tff(f_89, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.35/2.86  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 8.35/2.86  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.35/2.86  tff(f_121, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 8.35/2.86  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.35/2.86  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.35/2.86  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 8.35/2.86  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.35/2.86  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 8.35/2.86  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.35/2.86  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.35/2.86  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.35/2.86  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.35/2.86  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.35/2.86  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.35/2.86  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.35/2.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.35/2.86  tff(f_103, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 8.35/2.86  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.35/2.86  tff(f_117, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.35/2.86  tff(f_139, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.35/2.86  tff(c_54, plain, (![A_50, B_51]: (v1_relat_1(k2_zfmisc_1(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.35/2.86  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.35/2.86  tff(c_314, plain, (![B_104, A_105]: (v1_relat_1(B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_105)) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.35/2.86  tff(c_317, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_314])).
% 8.35/2.86  tff(c_323, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_317])).
% 8.35/2.86  tff(c_70, plain, (![B_61, A_60]: (r1_tarski(k7_relat_1(B_61, A_60), B_61) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.35/2.86  tff(c_46, plain, (![A_43, B_44]: (m1_subset_1(A_43, k1_zfmisc_1(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.35/2.86  tff(c_400, plain, (![A_114, B_115]: (v1_relat_1(A_114) | ~v1_relat_1(B_115) | ~r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_46, c_314])).
% 8.35/2.86  tff(c_419, plain, (![B_61, A_60]: (v1_relat_1(k7_relat_1(B_61, A_60)) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_70, c_400])).
% 8.35/2.86  tff(c_56, plain, (![B_53, A_52]: (k2_relat_1(k7_relat_1(B_53, A_52))=k9_relat_1(B_53, A_52) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.35/2.86  tff(c_1027, plain, (![A_182, B_183]: (r1_tarski(k2_relat_1(A_182), k2_relat_1(B_183)) | ~r1_tarski(A_182, B_183) | ~v1_relat_1(B_183) | ~v1_relat_1(A_182))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.35/2.86  tff(c_10793, plain, (![B_650, A_651, B_652]: (r1_tarski(k9_relat_1(B_650, A_651), k2_relat_1(B_652)) | ~r1_tarski(k7_relat_1(B_650, A_651), B_652) | ~v1_relat_1(B_652) | ~v1_relat_1(k7_relat_1(B_650, A_651)) | ~v1_relat_1(B_650))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1027])).
% 8.35/2.86  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.35/2.86  tff(c_38, plain, (![B_40]: (k2_zfmisc_1(k1_xboole_0, B_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.35/2.86  tff(c_1192, plain, (![B_199, A_200]: (k1_tarski(k1_funct_1(B_199, A_200))=k2_relat_1(B_199) | k1_tarski(A_200)!=k1_relat_1(B_199) | ~v1_funct_1(B_199) | ~v1_relat_1(B_199))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.35/2.86  tff(c_80, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.35/2.86  tff(c_1211, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1192, c_80])).
% 8.35/2.86  tff(c_1229, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_88, c_1211])).
% 8.35/2.86  tff(c_1286, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1229])).
% 8.35/2.86  tff(c_597, plain, (![C_149, A_150, B_151]: (v4_relat_1(C_149, A_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.35/2.86  tff(c_611, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_597])).
% 8.35/2.86  tff(c_14, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.35/2.86  tff(c_540, plain, (![B_142, A_143]: (r1_tarski(k1_relat_1(B_142), A_143) | ~v4_relat_1(B_142, A_143) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.35/2.86  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.35/2.86  tff(c_1624, plain, (![B_234, A_235]: (k3_xboole_0(k1_relat_1(B_234), A_235)=k1_relat_1(B_234) | ~v4_relat_1(B_234, A_235) | ~v1_relat_1(B_234))), inference(resolution, [status(thm)], [c_540, c_10])).
% 8.35/2.86  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.35/2.86  tff(c_1634, plain, (![B_234, A_235]: (k5_xboole_0(k1_relat_1(B_234), k1_relat_1(B_234))=k4_xboole_0(k1_relat_1(B_234), A_235) | ~v4_relat_1(B_234, A_235) | ~v1_relat_1(B_234))), inference(superposition, [status(thm), theory('equality')], [c_1624, c_8])).
% 8.35/2.86  tff(c_1662, plain, (![B_236, A_237]: (k4_xboole_0(k1_relat_1(B_236), A_237)=k1_xboole_0 | ~v4_relat_1(B_236, A_237) | ~v1_relat_1(B_236))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1634])).
% 8.35/2.86  tff(c_40, plain, (![B_42, A_41]: (~r2_hidden(B_42, A_41) | k4_xboole_0(A_41, k1_tarski(B_42))!=A_41)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.35/2.86  tff(c_3232, plain, (![B_337, B_338]: (~r2_hidden(B_337, k1_relat_1(B_338)) | k1_relat_1(B_338)!=k1_xboole_0 | ~v4_relat_1(B_338, k1_tarski(B_337)) | ~v1_relat_1(B_338))), inference(superposition, [status(thm), theory('equality')], [c_1662, c_40])).
% 8.35/2.86  tff(c_3266, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_4')) | k1_relat_1('#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_611, c_3232])).
% 8.35/2.86  tff(c_3282, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_4')) | k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_323, c_3266])).
% 8.35/2.86  tff(c_3286, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3282])).
% 8.35/2.86  tff(c_42, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k1_tarski(B_42))=A_41 | r2_hidden(B_42, A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.35/2.86  tff(c_3299, plain, (![B_341, B_342]: (k1_relat_1(B_341)=k1_xboole_0 | ~v4_relat_1(B_341, k1_tarski(B_342)) | ~v1_relat_1(B_341) | r2_hidden(B_342, k1_relat_1(B_341)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1662])).
% 8.35/2.86  tff(c_3333, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4') | r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_611, c_3299])).
% 8.35/2.86  tff(c_3349, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_3333])).
% 8.35/2.86  tff(c_3350, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3286, c_3349])).
% 8.35/2.86  tff(c_52, plain, (![B_49, A_48]: (r1_tarski(k1_relat_1(B_49), A_48) | ~v4_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.35/2.86  tff(c_32, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.35/2.86  tff(c_343, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(B_110, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.35/2.86  tff(c_1287, plain, (![A_208, B_209]: (k1_tarski(A_208)=B_209 | ~r1_tarski(B_209, k1_tarski(A_208)) | ~r2_hidden(A_208, B_209))), inference(resolution, [status(thm)], [c_32, c_343])).
% 8.35/2.86  tff(c_3771, plain, (![A_361, B_362]: (k1_tarski(A_361)=k1_relat_1(B_362) | ~r2_hidden(A_361, k1_relat_1(B_362)) | ~v4_relat_1(B_362, k1_tarski(A_361)) | ~v1_relat_1(B_362))), inference(resolution, [status(thm)], [c_52, c_1287])).
% 8.35/2.86  tff(c_3805, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~r2_hidden('#skF_1', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_611, c_3771])).
% 8.35/2.86  tff(c_3821, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_3350, c_3805])).
% 8.35/2.86  tff(c_3823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1286, c_3821])).
% 8.35/2.86  tff(c_3825, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3282])).
% 8.35/2.86  tff(c_60, plain, (![A_56]: (r1_tarski(A_56, k2_zfmisc_1(k1_relat_1(A_56), k2_relat_1(A_56))) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.35/2.86  tff(c_3913, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3825, c_60])).
% 8.35/2.86  tff(c_3982, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_323, c_38, c_3913])).
% 8.35/2.86  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.35/2.86  tff(c_361, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_343])).
% 8.35/2.86  tff(c_4045, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3982, c_361])).
% 8.35/2.86  tff(c_4113, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_4045, c_12])).
% 8.35/2.86  tff(c_129, plain, (![A_76, B_77]: (v1_relat_1(k2_zfmisc_1(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.35/2.86  tff(c_131, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_129])).
% 8.35/2.86  tff(c_66, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.35/2.86  tff(c_362, plain, (![A_112]: (k1_xboole_0=A_112 | ~r1_tarski(A_112, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_343])).
% 8.35/2.86  tff(c_366, plain, (![A_60]: (k7_relat_1(k1_xboole_0, A_60)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_70, c_362])).
% 8.35/2.86  tff(c_381, plain, (![A_60]: (k7_relat_1(k1_xboole_0, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_366])).
% 8.35/2.86  tff(c_434, plain, (![B_120, A_121]: (k2_relat_1(k7_relat_1(B_120, A_121))=k9_relat_1(B_120, A_121) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.35/2.86  tff(c_443, plain, (![A_60]: (k9_relat_1(k1_xboole_0, A_60)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_381, c_434])).
% 8.35/2.86  tff(c_447, plain, (![A_60]: (k9_relat_1(k1_xboole_0, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_66, c_443])).
% 8.35/2.86  tff(c_4097, plain, (![A_60]: (k9_relat_1('#skF_4', A_60)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4045, c_4045, c_447])).
% 8.35/2.86  tff(c_1442, plain, (![A_215, B_216, C_217, D_218]: (k7_relset_1(A_215, B_216, C_217, D_218)=k9_relat_1(C_217, D_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.35/2.86  tff(c_1452, plain, (![D_218]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_218)=k9_relat_1('#skF_4', D_218))), inference(resolution, [status(thm)], [c_84, c_1442])).
% 8.35/2.86  tff(c_1454, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_80])).
% 8.35/2.86  tff(c_4893, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4097, c_1454])).
% 8.35/2.86  tff(c_4897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4113, c_4893])).
% 8.35/2.86  tff(c_4899, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1229])).
% 8.35/2.86  tff(c_72, plain, (![B_63, A_62]: (k1_tarski(k1_funct_1(B_63, A_62))=k2_relat_1(B_63) | k1_tarski(A_62)!=k1_relat_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.35/2.86  tff(c_4908, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4899, c_84])).
% 8.35/2.86  tff(c_78, plain, (![A_67, B_68, C_69, D_70]: (k7_relset_1(A_67, B_68, C_69, D_70)=k9_relat_1(C_69, D_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.35/2.86  tff(c_5028, plain, (![D_70]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_70)=k9_relat_1('#skF_4', D_70))), inference(resolution, [status(thm)], [c_4908, c_78])).
% 8.35/2.86  tff(c_4905, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4899, c_80])).
% 8.35/2.86  tff(c_5283, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5028, c_4905])).
% 8.35/2.86  tff(c_5295, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72, c_5283])).
% 8.35/2.86  tff(c_5297, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_88, c_4899, c_5295])).
% 8.35/2.86  tff(c_10800, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10793, c_5297])).
% 8.35/2.86  tff(c_10849, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_10800])).
% 8.35/2.86  tff(c_10865, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_10849])).
% 8.35/2.86  tff(c_10868, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_419, c_10865])).
% 8.35/2.86  tff(c_10872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_10868])).
% 8.35/2.86  tff(c_10873, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_10849])).
% 8.35/2.86  tff(c_10882, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_10873])).
% 8.35/2.86  tff(c_10886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_10882])).
% 8.35/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.86  
% 8.35/2.86  Inference rules
% 8.35/2.86  ----------------------
% 8.35/2.86  #Ref     : 0
% 8.35/2.86  #Sup     : 2339
% 8.35/2.86  #Fact    : 0
% 8.35/2.86  #Define  : 0
% 8.35/2.86  #Split   : 9
% 8.35/2.86  #Chain   : 0
% 8.35/2.86  #Close   : 0
% 8.35/2.86  
% 8.35/2.86  Ordering : KBO
% 8.35/2.86  
% 8.35/2.86  Simplification rules
% 8.35/2.86  ----------------------
% 8.35/2.86  #Subsume      : 417
% 8.35/2.86  #Demod        : 2549
% 8.35/2.86  #Tautology    : 1052
% 8.35/2.86  #SimpNegUnit  : 61
% 8.35/2.86  #BackRed      : 83
% 8.35/2.86  
% 8.35/2.86  #Partial instantiations: 0
% 8.35/2.86  #Strategies tried      : 1
% 8.35/2.86  
% 8.35/2.86  Timing (in seconds)
% 8.35/2.86  ----------------------
% 8.35/2.87  Preprocessing        : 0.35
% 8.35/2.87  Parsing              : 0.18
% 8.35/2.87  CNF conversion       : 0.02
% 8.35/2.87  Main loop            : 1.74
% 8.35/2.87  Inferencing          : 0.54
% 8.35/2.87  Reduction            : 0.63
% 8.35/2.87  Demodulation         : 0.47
% 8.35/2.87  BG Simplification    : 0.06
% 8.35/2.87  Subsumption          : 0.39
% 8.35/2.87  Abstraction          : 0.07
% 8.35/2.87  MUC search           : 0.00
% 8.35/2.87  Cooper               : 0.00
% 8.35/2.87  Total                : 2.13
% 8.35/2.87  Index Insertion      : 0.00
% 8.35/2.87  Index Deletion       : 0.00
% 8.35/2.87  Index Matching       : 0.00
% 8.35/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
