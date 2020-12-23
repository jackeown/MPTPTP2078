%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:32 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 115 expanded)
%              Number of leaves         :   41 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 166 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(C,B)
     => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1259,plain,(
    ! [A_205,B_206,D_207] :
      ( r2_relset_1(A_205,B_206,D_207,D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1269,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1259])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_265,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k1_xboole_0
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_287,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_265])).

tff(c_354,plain,(
    ! [A_96,C_97,B_98] :
      ( r1_xboole_0(A_96,k4_xboole_0(C_97,B_98))
      | ~ r1_tarski(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_368,plain,(
    ! [A_100,A_101] :
      ( r1_xboole_0(A_100,k1_xboole_0)
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_354])).

tff(c_385,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_368])).

tff(c_768,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_tarski(A_147,B_148)
      | ~ r1_xboole_0(A_147,C_149)
      | ~ r1_tarski(A_147,k2_xboole_0(B_148,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_814,plain,(
    ! [A_150,B_151] :
      ( r1_tarski(A_150,A_150)
      | ~ r1_xboole_0(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_14,c_768])).

tff(c_822,plain,(
    ! [A_152] : r1_tarski(A_152,A_152) ),
    inference(resolution,[status(thm)],[c_385,c_814])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_391,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_403,plain,(
    ! [A_20,A_104,B_105] :
      ( v1_relat_1(A_20)
      | ~ r1_tarski(A_20,k2_zfmisc_1(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_24,c_391])).

tff(c_852,plain,(
    ! [A_104,B_105] : v1_relat_1(k2_zfmisc_1(A_104,B_105)) ),
    inference(resolution,[status(thm)],[c_822,c_403])).

tff(c_339,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_350,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_339])).

tff(c_353,plain,(
    ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_353])).

tff(c_860,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_1537,plain,(
    ! [A_236,B_237,C_238] :
      ( k1_relset_1(A_236,B_237,C_238) = k1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1550,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1537])).

tff(c_1637,plain,(
    ! [A_254,B_255,C_256] :
      ( m1_subset_1(k1_relset_1(A_254,B_255,C_256),k1_zfmisc_1(A_254))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1662,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_1637])).

tff(c_1672,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1662])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1750,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1672,c_22])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1786,plain,(
    k4_xboole_0(k1_relat_1('#skF_4'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1750,c_4])).

tff(c_1870,plain,(
    ! [A_265,B_266,C_267] :
      ( k2_xboole_0(k4_xboole_0(A_265,B_266),k3_xboole_0(A_265,k4_xboole_0(B_266,C_267))) = k4_xboole_0(A_265,C_267)
      | ~ r1_tarski(C_267,B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2635,plain,(
    ! [A_307,B_308,C_309] :
      ( r1_tarski(k4_xboole_0(A_307,B_308),k4_xboole_0(A_307,C_309))
      | ~ r1_tarski(C_309,B_308) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_14])).

tff(c_4695,plain,(
    ! [B_386] :
      ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_4'),B_386),k1_xboole_0)
      | ~ r1_tarski('#skF_2',B_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_2635])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4782,plain,(
    ! [B_388] :
      ( k4_xboole_0(k1_relat_1('#skF_4'),B_388) = k1_xboole_0
      | ~ r1_tarski('#skF_2',B_388) ) ),
    inference(resolution,[status(thm)],[c_4695,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1055,plain,(
    ! [B_176,A_177] :
      ( k7_relat_1(B_176,A_177) = B_176
      | ~ r1_tarski(k1_relat_1(B_176),A_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1064,plain,(
    ! [B_176,B_2] :
      ( k7_relat_1(B_176,B_2) = B_176
      | ~ v1_relat_1(B_176)
      | k4_xboole_0(k1_relat_1(B_176),B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_1055])).

tff(c_4798,plain,(
    ! [B_388] :
      ( k7_relat_1('#skF_4',B_388) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_388) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4782,c_1064])).

tff(c_5041,plain,(
    ! [B_392] :
      ( k7_relat_1('#skF_4',B_392) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_4798])).

tff(c_5121,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_5041])).

tff(c_1812,plain,(
    ! [A_260,B_261,C_262,D_263] :
      ( k5_relset_1(A_260,B_261,C_262,D_263) = k7_relat_1(C_262,D_263)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1826,plain,(
    ! [D_263] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_263) = k7_relat_1('#skF_4',D_263) ),
    inference(resolution,[status(thm)],[c_52,c_1812])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1832,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_48])).

tff(c_5122,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5121,c_1832])).

tff(c_5125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_5122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.25/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/1.99  
% 5.25/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/1.99  %$ r2_relset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_relset_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.25/1.99  
% 5.25/1.99  %Foreground sorts:
% 5.25/1.99  
% 5.25/1.99  
% 5.25/1.99  %Background operators:
% 5.25/1.99  
% 5.25/1.99  
% 5.25/1.99  %Foreground operators:
% 5.25/1.99  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.25/1.99  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 5.25/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.25/1.99  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.25/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.25/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.25/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.25/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.25/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.25/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.25/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.25/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.25/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.25/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.25/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.25/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.25/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.25/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.25/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.25/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.25/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.25/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.25/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.25/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.25/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.25/1.99  
% 5.25/2.01  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 5.25/2.01  tff(f_114, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.25/2.01  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.25/2.01  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.25/2.01  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.25/2.01  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.25/2.01  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.25/2.01  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.25/2.01  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.25/2.01  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.25/2.01  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.25/2.01  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.25/2.01  tff(f_33, axiom, (![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 5.25/2.01  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.25/2.01  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.25/2.01  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 5.25/2.01  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.25/2.01  tff(c_1259, plain, (![A_205, B_206, D_207]: (r2_relset_1(A_205, B_206, D_207, D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.25/2.01  tff(c_1269, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1259])).
% 5.25/2.01  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.25/2.01  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.25/2.01  tff(c_20, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.25/2.01  tff(c_56, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.25/2.01  tff(c_64, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_20, c_56])).
% 5.25/2.01  tff(c_265, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k1_xboole_0 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.25/2.01  tff(c_287, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_265])).
% 5.25/2.01  tff(c_354, plain, (![A_96, C_97, B_98]: (r1_xboole_0(A_96, k4_xboole_0(C_97, B_98)) | ~r1_tarski(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.25/2.01  tff(c_368, plain, (![A_100, A_101]: (r1_xboole_0(A_100, k1_xboole_0) | ~r1_tarski(A_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_287, c_354])).
% 5.25/2.01  tff(c_385, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_368])).
% 5.25/2.01  tff(c_768, plain, (![A_147, B_148, C_149]: (r1_tarski(A_147, B_148) | ~r1_xboole_0(A_147, C_149) | ~r1_tarski(A_147, k2_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.25/2.01  tff(c_814, plain, (![A_150, B_151]: (r1_tarski(A_150, A_150) | ~r1_xboole_0(A_150, B_151))), inference(resolution, [status(thm)], [c_14, c_768])).
% 5.25/2.01  tff(c_822, plain, (![A_152]: (r1_tarski(A_152, A_152))), inference(resolution, [status(thm)], [c_385, c_814])).
% 5.25/2.01  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.25/2.01  tff(c_391, plain, (![C_103, A_104, B_105]: (v1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.25/2.01  tff(c_403, plain, (![A_20, A_104, B_105]: (v1_relat_1(A_20) | ~r1_tarski(A_20, k2_zfmisc_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_24, c_391])).
% 5.25/2.01  tff(c_852, plain, (![A_104, B_105]: (v1_relat_1(k2_zfmisc_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_822, c_403])).
% 5.25/2.01  tff(c_339, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.25/2.01  tff(c_350, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_339])).
% 5.25/2.01  tff(c_353, plain, (~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_350])).
% 5.25/2.01  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_852, c_353])).
% 5.25/2.01  tff(c_860, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_350])).
% 5.25/2.01  tff(c_1537, plain, (![A_236, B_237, C_238]: (k1_relset_1(A_236, B_237, C_238)=k1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.25/2.01  tff(c_1550, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1537])).
% 5.25/2.01  tff(c_1637, plain, (![A_254, B_255, C_256]: (m1_subset_1(k1_relset_1(A_254, B_255, C_256), k1_zfmisc_1(A_254)) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.25/2.01  tff(c_1662, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1550, c_1637])).
% 5.25/2.01  tff(c_1672, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1662])).
% 5.25/2.01  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.25/2.01  tff(c_1750, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_1672, c_22])).
% 5.25/2.01  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.25/2.01  tff(c_1786, plain, (k4_xboole_0(k1_relat_1('#skF_4'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1750, c_4])).
% 5.25/2.01  tff(c_1870, plain, (![A_265, B_266, C_267]: (k2_xboole_0(k4_xboole_0(A_265, B_266), k3_xboole_0(A_265, k4_xboole_0(B_266, C_267)))=k4_xboole_0(A_265, C_267) | ~r1_tarski(C_267, B_266))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.25/2.01  tff(c_2635, plain, (![A_307, B_308, C_309]: (r1_tarski(k4_xboole_0(A_307, B_308), k4_xboole_0(A_307, C_309)) | ~r1_tarski(C_309, B_308))), inference(superposition, [status(thm), theory('equality')], [c_1870, c_14])).
% 5.25/2.01  tff(c_4695, plain, (![B_386]: (r1_tarski(k4_xboole_0(k1_relat_1('#skF_4'), B_386), k1_xboole_0) | ~r1_tarski('#skF_2', B_386))), inference(superposition, [status(thm), theory('equality')], [c_1786, c_2635])).
% 5.25/2.01  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.25/2.01  tff(c_4782, plain, (![B_388]: (k4_xboole_0(k1_relat_1('#skF_4'), B_388)=k1_xboole_0 | ~r1_tarski('#skF_2', B_388))), inference(resolution, [status(thm)], [c_4695, c_8])).
% 5.25/2.01  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.25/2.01  tff(c_1055, plain, (![B_176, A_177]: (k7_relat_1(B_176, A_177)=B_176 | ~r1_tarski(k1_relat_1(B_176), A_177) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.25/2.01  tff(c_1064, plain, (![B_176, B_2]: (k7_relat_1(B_176, B_2)=B_176 | ~v1_relat_1(B_176) | k4_xboole_0(k1_relat_1(B_176), B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1055])).
% 5.25/2.01  tff(c_4798, plain, (![B_388]: (k7_relat_1('#skF_4', B_388)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_388))), inference(superposition, [status(thm), theory('equality')], [c_4782, c_1064])).
% 5.25/2.01  tff(c_5041, plain, (![B_392]: (k7_relat_1('#skF_4', B_392)='#skF_4' | ~r1_tarski('#skF_2', B_392))), inference(demodulation, [status(thm), theory('equality')], [c_860, c_4798])).
% 5.25/2.01  tff(c_5121, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_5041])).
% 5.25/2.01  tff(c_1812, plain, (![A_260, B_261, C_262, D_263]: (k5_relset_1(A_260, B_261, C_262, D_263)=k7_relat_1(C_262, D_263) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.25/2.01  tff(c_1826, plain, (![D_263]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_263)=k7_relat_1('#skF_4', D_263))), inference(resolution, [status(thm)], [c_52, c_1812])).
% 5.25/2.01  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.25/2.01  tff(c_1832, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1826, c_48])).
% 5.25/2.01  tff(c_5122, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5121, c_1832])).
% 5.25/2.01  tff(c_5125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1269, c_5122])).
% 5.25/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.01  
% 5.25/2.01  Inference rules
% 5.25/2.01  ----------------------
% 5.25/2.01  #Ref     : 0
% 5.25/2.01  #Sup     : 1131
% 5.25/2.01  #Fact    : 0
% 5.25/2.01  #Define  : 0
% 5.25/2.01  #Split   : 13
% 5.25/2.01  #Chain   : 0
% 5.25/2.01  #Close   : 0
% 5.25/2.01  
% 5.25/2.01  Ordering : KBO
% 5.25/2.01  
% 5.25/2.01  Simplification rules
% 5.25/2.01  ----------------------
% 5.25/2.01  #Subsume      : 111
% 5.25/2.01  #Demod        : 592
% 5.25/2.01  #Tautology    : 535
% 5.25/2.01  #SimpNegUnit  : 17
% 5.25/2.01  #BackRed      : 12
% 5.25/2.01  
% 5.25/2.01  #Partial instantiations: 0
% 5.25/2.01  #Strategies tried      : 1
% 5.25/2.01  
% 5.25/2.01  Timing (in seconds)
% 5.25/2.01  ----------------------
% 5.25/2.01  Preprocessing        : 0.33
% 5.25/2.01  Parsing              : 0.18
% 5.25/2.01  CNF conversion       : 0.02
% 5.25/2.01  Main loop            : 0.92
% 5.25/2.01  Inferencing          : 0.30
% 5.25/2.01  Reduction            : 0.33
% 5.25/2.01  Demodulation         : 0.24
% 5.25/2.01  BG Simplification    : 0.03
% 5.25/2.01  Subsumption          : 0.17
% 5.25/2.01  Abstraction          : 0.04
% 5.25/2.01  MUC search           : 0.00
% 5.25/2.01  Cooper               : 0.00
% 5.25/2.01  Total                : 1.28
% 5.25/2.01  Index Insertion      : 0.00
% 5.25/2.01  Index Deletion       : 0.00
% 5.25/2.01  Index Matching       : 0.00
% 5.25/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
