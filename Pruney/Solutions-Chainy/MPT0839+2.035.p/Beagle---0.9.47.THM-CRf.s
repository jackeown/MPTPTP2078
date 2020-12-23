%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:26 EST 2020

% Result     : Theorem 14.69s
% Output     : CNFRefutation 14.69s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 271 expanded)
%              Number of leaves         :   46 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  205 ( 551 expanded)
%              Number of equality atoms :   49 ( 102 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_58,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34425,plain,(
    ! [A_631,B_632,C_633] :
      ( k2_relset_1(A_631,B_632,C_633) = k2_relat_1(C_633)
      | ~ m1_subset_1(C_633,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34441,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_34425])).

tff(c_68,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34442,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34441,c_68])).

tff(c_52,plain,(
    ! [A_41,B_42] : v1_relat_1(k2_zfmisc_1(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_134,plain,(
    ! [B_87,A_88] :
      ( v1_relat_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_144,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_134])).

tff(c_151,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_144])).

tff(c_784,plain,(
    ! [A_151,B_152,C_153] :
      ( k2_relset_1(A_151,B_152,C_153) = k2_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_800,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_784])).

tff(c_801,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_68])).

tff(c_54,plain,(
    ! [A_43] :
      ( k10_relat_1(A_43,k2_relat_1(A_43)) = k1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_880,plain,(
    ! [B_163,A_164] :
      ( k10_relat_1(B_163,A_164) != k1_xboole_0
      | ~ r1_tarski(A_164,k2_relat_1(B_163))
      | k1_xboole_0 = A_164
      | ~ v1_relat_1(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2545,plain,(
    ! [B_219] :
      ( k10_relat_1(B_219,k2_relat_1(B_219)) != k1_xboole_0
      | k2_relat_1(B_219) = k1_xboole_0
      | ~ v1_relat_1(B_219) ) ),
    inference(resolution,[status(thm)],[c_12,c_880])).

tff(c_2872,plain,(
    ! [A_240] :
      ( k1_relat_1(A_240) != k1_xboole_0
      | k2_relat_1(A_240) = k1_xboole_0
      | ~ v1_relat_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2545])).

tff(c_2876,plain,
    ( k1_relat_1('#skF_8') != k1_xboole_0
    | k2_relat_1('#skF_8') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_151,c_2872])).

tff(c_2882,plain,
    ( k1_relat_1('#skF_8') != k1_xboole_0
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_2876])).

tff(c_2883,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_801,c_2882])).

tff(c_247,plain,(
    ! [C_109,A_110,B_111] :
      ( v4_relat_1(C_109,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_263,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_247])).

tff(c_50,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k1_relat_1(B_40),A_39)
      | ~ v4_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_28] : k3_tarski(k1_zfmisc_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [C_123,A_124,D_125] :
      ( r2_hidden(C_123,k3_tarski(A_124))
      | ~ r2_hidden(D_125,A_124)
      | ~ r2_hidden(C_123,D_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_327,plain,(
    ! [C_127,A_128] :
      ( r2_hidden(C_127,k3_tarski(A_128))
      | ~ r2_hidden(C_127,'#skF_1'(A_128))
      | v1_xboole_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_4,c_314])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1044,plain,(
    ! [A_166,C_167] :
      ( ~ v1_xboole_0(k3_tarski(A_166))
      | ~ r2_hidden(C_167,'#skF_1'(A_166))
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_327,c_2])).

tff(c_1060,plain,(
    ! [A_168] :
      ( ~ v1_xboole_0(k3_tarski(A_168))
      | v1_xboole_0(A_168)
      | v1_xboole_0('#skF_1'(A_168)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1044])).

tff(c_1084,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(A_28)
      | v1_xboole_0(k1_zfmisc_1(A_28))
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_28))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1060])).

tff(c_1097,plain,(
    ! [A_169] :
      ( ~ v1_xboole_0(A_169)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_169))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1084])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [B_74,A_75] :
      ( ~ v1_xboole_0(B_74)
      | B_74 = A_75
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    ! [A_75] :
      ( k1_xboole_0 = A_75
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_1116,plain,(
    ! [A_169] :
      ( '#skF_1'(k1_zfmisc_1(A_169)) = k1_xboole_0
      | ~ v1_xboole_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_1097,c_92])).

tff(c_338,plain,(
    ! [C_127,A_28] :
      ( r2_hidden(C_127,A_28)
      | ~ r2_hidden(C_127,'#skF_1'(k1_zfmisc_1(A_28)))
      | v1_xboole_0(k1_zfmisc_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_327])).

tff(c_670,plain,(
    ! [C_146,A_147] :
      ( r2_hidden(C_146,A_147)
      | ~ r2_hidden(C_146,'#skF_1'(k1_zfmisc_1(A_147))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_338])).

tff(c_2969,plain,(
    ! [A_250] :
      ( r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_250))),A_250)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_250))) ) ),
    inference(resolution,[status(thm)],[c_4,c_670])).

tff(c_819,plain,(
    ! [A_156,B_157,C_158] :
      ( k1_relset_1(A_156,B_157,C_158) = k1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_835,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_819])).

tff(c_66,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,k1_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ m1_subset_1(D_66,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_839,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,k1_relat_1('#skF_8'))
      | ~ m1_subset_1(D_66,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_66])).

tff(c_3023,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k1_relat_1('#skF_8')))),'#skF_7')
    | v1_xboole_0('#skF_1'(k1_zfmisc_1(k1_relat_1('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_2969,c_839])).

tff(c_3201,plain,(
    ~ m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k1_relat_1('#skF_8')))),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3023])).

tff(c_3282,plain,
    ( ~ m1_subset_1('#skF_1'(k1_xboole_0),'#skF_7')
    | ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_3201])).

tff(c_3524,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3282])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6018,plain,(
    ! [C_317,B_318,A_319] :
      ( r2_hidden(C_317,k3_tarski(B_318))
      | ~ r2_hidden(C_317,A_319)
      | v1_xboole_0(B_318)
      | ~ m1_subset_1(A_319,B_318) ) ),
    inference(resolution,[status(thm)],[c_40,c_314])).

tff(c_30779,plain,(
    ! [A_547,B_548] :
      ( r2_hidden('#skF_1'(A_547),k3_tarski(B_548))
      | v1_xboole_0(B_548)
      | ~ m1_subset_1(A_547,B_548)
      | v1_xboole_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_4,c_6018])).

tff(c_30960,plain,(
    ! [A_547,A_28] :
      ( r2_hidden('#skF_1'(A_547),A_28)
      | v1_xboole_0(k1_zfmisc_1(A_28))
      | ~ m1_subset_1(A_547,k1_zfmisc_1(A_28))
      | v1_xboole_0(A_547) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_30779])).

tff(c_31381,plain,(
    ! [A_555,A_556] :
      ( r2_hidden('#skF_1'(A_555),A_556)
      | ~ m1_subset_1(A_555,k1_zfmisc_1(A_556))
      | v1_xboole_0(A_555) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_30960])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_33922,plain,(
    ! [A_586,A_587] :
      ( m1_subset_1('#skF_1'(A_586),A_587)
      | ~ m1_subset_1(A_586,k1_zfmisc_1(A_587))
      | v1_xboole_0(A_586) ) ),
    inference(resolution,[status(thm)],[c_31381,c_38])).

tff(c_128,plain,(
    ! [D_86] :
      ( ~ r2_hidden(D_86,k1_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ m1_subset_1(D_86,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_133,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_7','#skF_6','#skF_8')),'#skF_7')
    | v1_xboole_0(k1_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_221,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_7','#skF_6','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_838,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_221])).

tff(c_33948,plain,
    ( ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_33922,c_838])).

tff(c_34032,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_3524,c_33948])).

tff(c_34060,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_34032])).

tff(c_34063,plain,
    ( ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_34060])).

tff(c_34067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_263,c_34063])).

tff(c_34069,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3282])).

tff(c_34092,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34069,c_92])).

tff(c_34107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2883,c_34092])).

tff(c_34108,plain,(
    v1_xboole_0(k1_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_34115,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34108,c_92])).

tff(c_34647,plain,(
    ! [A_643,B_644,C_645] :
      ( k1_relset_1(A_643,B_644,C_645) = k1_relat_1(C_645)
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(A_643,B_644))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34662,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_34647])).

tff(c_34669,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34115,c_34662])).

tff(c_34588,plain,(
    ! [B_639,A_640] :
      ( k10_relat_1(B_639,A_640) != k1_xboole_0
      | ~ r1_tarski(A_640,k2_relat_1(B_639))
      | k1_xboole_0 = A_640
      | ~ v1_relat_1(B_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36537,plain,(
    ! [B_718] :
      ( k10_relat_1(B_718,k2_relat_1(B_718)) != k1_xboole_0
      | k2_relat_1(B_718) = k1_xboole_0
      | ~ v1_relat_1(B_718) ) ),
    inference(resolution,[status(thm)],[c_12,c_34588])).

tff(c_36668,plain,(
    ! [A_732] :
      ( k1_relat_1(A_732) != k1_xboole_0
      | k2_relat_1(A_732) = k1_xboole_0
      | ~ v1_relat_1(A_732)
      | ~ v1_relat_1(A_732) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_36537])).

tff(c_36674,plain,
    ( k1_relat_1('#skF_8') != k1_xboole_0
    | k2_relat_1('#skF_8') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_151,c_36668])).

tff(c_36681,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_34669,c_36674])).

tff(c_36683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34442,c_36681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.69/6.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.69/6.05  
% 14.69/6.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.69/6.05  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 14.69/6.05  
% 14.69/6.05  %Foreground sorts:
% 14.69/6.05  
% 14.69/6.05  
% 14.69/6.05  %Background operators:
% 14.69/6.05  
% 14.69/6.05  
% 14.69/6.05  %Foreground operators:
% 14.69/6.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.69/6.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.69/6.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.69/6.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.69/6.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.69/6.05  tff('#skF_7', type, '#skF_7': $i).
% 14.69/6.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.69/6.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.69/6.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.69/6.05  tff('#skF_6', type, '#skF_6': $i).
% 14.69/6.05  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.69/6.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.69/6.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.69/6.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.69/6.05  tff('#skF_8', type, '#skF_8': $i).
% 14.69/6.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.69/6.05  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 14.69/6.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.69/6.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.69/6.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.69/6.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.69/6.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.69/6.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.69/6.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.69/6.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.69/6.05  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.69/6.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.69/6.05  
% 14.69/6.07  tff(f_139, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 14.69/6.07  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.69/6.07  tff(f_90, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.69/6.07  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.69/6.07  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 14.69/6.07  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.69/6.07  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 14.69/6.07  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.69/6.07  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 14.69/6.07  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.69/6.07  tff(f_61, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 14.69/6.07  tff(f_58, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 14.69/6.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.69/6.07  tff(f_56, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 14.69/6.07  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.69/6.07  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 14.69/6.07  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.69/6.07  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 14.69/6.07  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 14.69/6.07  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.69/6.07  tff(c_34425, plain, (![A_631, B_632, C_633]: (k2_relset_1(A_631, B_632, C_633)=k2_relat_1(C_633) | ~m1_subset_1(C_633, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.69/6.07  tff(c_34441, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_34425])).
% 14.69/6.07  tff(c_68, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.69/6.07  tff(c_34442, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34441, c_68])).
% 14.69/6.07  tff(c_52, plain, (![A_41, B_42]: (v1_relat_1(k2_zfmisc_1(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.69/6.07  tff(c_134, plain, (![B_87, A_88]: (v1_relat_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.69/6.07  tff(c_144, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_134])).
% 14.69/6.07  tff(c_151, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_144])).
% 14.69/6.07  tff(c_784, plain, (![A_151, B_152, C_153]: (k2_relset_1(A_151, B_152, C_153)=k2_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.69/6.07  tff(c_800, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_784])).
% 14.69/6.07  tff(c_801, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_800, c_68])).
% 14.69/6.07  tff(c_54, plain, (![A_43]: (k10_relat_1(A_43, k2_relat_1(A_43))=k1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_94])).
% 14.69/6.07  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.69/6.07  tff(c_880, plain, (![B_163, A_164]: (k10_relat_1(B_163, A_164)!=k1_xboole_0 | ~r1_tarski(A_164, k2_relat_1(B_163)) | k1_xboole_0=A_164 | ~v1_relat_1(B_163))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.69/6.07  tff(c_2545, plain, (![B_219]: (k10_relat_1(B_219, k2_relat_1(B_219))!=k1_xboole_0 | k2_relat_1(B_219)=k1_xboole_0 | ~v1_relat_1(B_219))), inference(resolution, [status(thm)], [c_12, c_880])).
% 14.69/6.07  tff(c_2872, plain, (![A_240]: (k1_relat_1(A_240)!=k1_xboole_0 | k2_relat_1(A_240)=k1_xboole_0 | ~v1_relat_1(A_240) | ~v1_relat_1(A_240))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2545])).
% 14.69/6.07  tff(c_2876, plain, (k1_relat_1('#skF_8')!=k1_xboole_0 | k2_relat_1('#skF_8')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_151, c_2872])).
% 14.69/6.07  tff(c_2882, plain, (k1_relat_1('#skF_8')!=k1_xboole_0 | k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151, c_2876])).
% 14.69/6.07  tff(c_2883, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_801, c_2882])).
% 14.69/6.07  tff(c_247, plain, (![C_109, A_110, B_111]: (v4_relat_1(C_109, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.69/6.07  tff(c_263, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_247])).
% 14.69/6.07  tff(c_50, plain, (![B_40, A_39]: (r1_tarski(k1_relat_1(B_40), A_39) | ~v4_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.69/6.07  tff(c_44, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.69/6.07  tff(c_36, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.07  tff(c_34, plain, (![A_28]: (k3_tarski(k1_zfmisc_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.69/6.07  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.69/6.07  tff(c_314, plain, (![C_123, A_124, D_125]: (r2_hidden(C_123, k3_tarski(A_124)) | ~r2_hidden(D_125, A_124) | ~r2_hidden(C_123, D_125))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.69/6.07  tff(c_327, plain, (![C_127, A_128]: (r2_hidden(C_127, k3_tarski(A_128)) | ~r2_hidden(C_127, '#skF_1'(A_128)) | v1_xboole_0(A_128))), inference(resolution, [status(thm)], [c_4, c_314])).
% 14.69/6.07  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.69/6.07  tff(c_1044, plain, (![A_166, C_167]: (~v1_xboole_0(k3_tarski(A_166)) | ~r2_hidden(C_167, '#skF_1'(A_166)) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_327, c_2])).
% 14.69/6.07  tff(c_1060, plain, (![A_168]: (~v1_xboole_0(k3_tarski(A_168)) | v1_xboole_0(A_168) | v1_xboole_0('#skF_1'(A_168)))), inference(resolution, [status(thm)], [c_4, c_1044])).
% 14.69/6.07  tff(c_1084, plain, (![A_28]: (~v1_xboole_0(A_28) | v1_xboole_0(k1_zfmisc_1(A_28)) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_28))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1060])).
% 14.69/6.07  tff(c_1097, plain, (![A_169]: (~v1_xboole_0(A_169) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_169))))), inference(negUnitSimplification, [status(thm)], [c_36, c_1084])).
% 14.69/6.07  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.69/6.07  tff(c_89, plain, (![B_74, A_75]: (~v1_xboole_0(B_74) | B_74=A_75 | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.69/6.07  tff(c_92, plain, (![A_75]: (k1_xboole_0=A_75 | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_6, c_89])).
% 14.69/6.07  tff(c_1116, plain, (![A_169]: ('#skF_1'(k1_zfmisc_1(A_169))=k1_xboole_0 | ~v1_xboole_0(A_169))), inference(resolution, [status(thm)], [c_1097, c_92])).
% 14.69/6.07  tff(c_338, plain, (![C_127, A_28]: (r2_hidden(C_127, A_28) | ~r2_hidden(C_127, '#skF_1'(k1_zfmisc_1(A_28))) | v1_xboole_0(k1_zfmisc_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_327])).
% 14.69/6.07  tff(c_670, plain, (![C_146, A_147]: (r2_hidden(C_146, A_147) | ~r2_hidden(C_146, '#skF_1'(k1_zfmisc_1(A_147))))), inference(negUnitSimplification, [status(thm)], [c_36, c_338])).
% 14.69/6.07  tff(c_2969, plain, (![A_250]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_250))), A_250) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_250))))), inference(resolution, [status(thm)], [c_4, c_670])).
% 14.69/6.07  tff(c_819, plain, (![A_156, B_157, C_158]: (k1_relset_1(A_156, B_157, C_158)=k1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.69/6.07  tff(c_835, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_819])).
% 14.69/6.07  tff(c_66, plain, (![D_66]: (~r2_hidden(D_66, k1_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~m1_subset_1(D_66, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.69/6.07  tff(c_839, plain, (![D_66]: (~r2_hidden(D_66, k1_relat_1('#skF_8')) | ~m1_subset_1(D_66, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_66])).
% 14.69/6.07  tff(c_3023, plain, (~m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k1_relat_1('#skF_8')))), '#skF_7') | v1_xboole_0('#skF_1'(k1_zfmisc_1(k1_relat_1('#skF_8'))))), inference(resolution, [status(thm)], [c_2969, c_839])).
% 14.69/6.07  tff(c_3201, plain, (~m1_subset_1('#skF_1'('#skF_1'(k1_zfmisc_1(k1_relat_1('#skF_8')))), '#skF_7')), inference(splitLeft, [status(thm)], [c_3023])).
% 14.69/6.07  tff(c_3282, plain, (~m1_subset_1('#skF_1'(k1_xboole_0), '#skF_7') | ~v1_xboole_0(k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1116, c_3201])).
% 14.69/6.07  tff(c_3524, plain, (~v1_xboole_0(k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_3282])).
% 14.69/6.07  tff(c_40, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.69/6.07  tff(c_6018, plain, (![C_317, B_318, A_319]: (r2_hidden(C_317, k3_tarski(B_318)) | ~r2_hidden(C_317, A_319) | v1_xboole_0(B_318) | ~m1_subset_1(A_319, B_318))), inference(resolution, [status(thm)], [c_40, c_314])).
% 14.69/6.07  tff(c_30779, plain, (![A_547, B_548]: (r2_hidden('#skF_1'(A_547), k3_tarski(B_548)) | v1_xboole_0(B_548) | ~m1_subset_1(A_547, B_548) | v1_xboole_0(A_547))), inference(resolution, [status(thm)], [c_4, c_6018])).
% 14.69/6.07  tff(c_30960, plain, (![A_547, A_28]: (r2_hidden('#skF_1'(A_547), A_28) | v1_xboole_0(k1_zfmisc_1(A_28)) | ~m1_subset_1(A_547, k1_zfmisc_1(A_28)) | v1_xboole_0(A_547))), inference(superposition, [status(thm), theory('equality')], [c_34, c_30779])).
% 14.69/6.07  tff(c_31381, plain, (![A_555, A_556]: (r2_hidden('#skF_1'(A_555), A_556) | ~m1_subset_1(A_555, k1_zfmisc_1(A_556)) | v1_xboole_0(A_555))), inference(negUnitSimplification, [status(thm)], [c_36, c_30960])).
% 14.69/6.07  tff(c_38, plain, (![A_30, B_31]: (m1_subset_1(A_30, B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.69/6.07  tff(c_33922, plain, (![A_586, A_587]: (m1_subset_1('#skF_1'(A_586), A_587) | ~m1_subset_1(A_586, k1_zfmisc_1(A_587)) | v1_xboole_0(A_586))), inference(resolution, [status(thm)], [c_31381, c_38])).
% 14.69/6.07  tff(c_128, plain, (![D_86]: (~r2_hidden(D_86, k1_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~m1_subset_1(D_86, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.69/6.07  tff(c_133, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_7', '#skF_6', '#skF_8')), '#skF_7') | v1_xboole_0(k1_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_4, c_128])).
% 14.69/6.07  tff(c_221, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_7', '#skF_6', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_133])).
% 14.69/6.07  tff(c_838, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_835, c_221])).
% 14.69/6.07  tff(c_33948, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | v1_xboole_0(k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_33922, c_838])).
% 14.69/6.07  tff(c_34032, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_3524, c_33948])).
% 14.69/6.07  tff(c_34060, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_44, c_34032])).
% 14.69/6.07  tff(c_34063, plain, (~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_34060])).
% 14.69/6.07  tff(c_34067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_263, c_34063])).
% 14.69/6.07  tff(c_34069, plain, (v1_xboole_0(k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_3282])).
% 14.69/6.07  tff(c_34092, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_34069, c_92])).
% 14.69/6.07  tff(c_34107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2883, c_34092])).
% 14.69/6.07  tff(c_34108, plain, (v1_xboole_0(k1_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_133])).
% 14.69/6.07  tff(c_34115, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_34108, c_92])).
% 14.69/6.07  tff(c_34647, plain, (![A_643, B_644, C_645]: (k1_relset_1(A_643, B_644, C_645)=k1_relat_1(C_645) | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(A_643, B_644))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.69/6.07  tff(c_34662, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_34647])).
% 14.69/6.07  tff(c_34669, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34115, c_34662])).
% 14.69/6.07  tff(c_34588, plain, (![B_639, A_640]: (k10_relat_1(B_639, A_640)!=k1_xboole_0 | ~r1_tarski(A_640, k2_relat_1(B_639)) | k1_xboole_0=A_640 | ~v1_relat_1(B_639))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.69/6.07  tff(c_36537, plain, (![B_718]: (k10_relat_1(B_718, k2_relat_1(B_718))!=k1_xboole_0 | k2_relat_1(B_718)=k1_xboole_0 | ~v1_relat_1(B_718))), inference(resolution, [status(thm)], [c_12, c_34588])).
% 14.69/6.07  tff(c_36668, plain, (![A_732]: (k1_relat_1(A_732)!=k1_xboole_0 | k2_relat_1(A_732)=k1_xboole_0 | ~v1_relat_1(A_732) | ~v1_relat_1(A_732))), inference(superposition, [status(thm), theory('equality')], [c_54, c_36537])).
% 14.69/6.07  tff(c_36674, plain, (k1_relat_1('#skF_8')!=k1_xboole_0 | k2_relat_1('#skF_8')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_151, c_36668])).
% 14.69/6.07  tff(c_36681, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151, c_34669, c_36674])).
% 14.69/6.07  tff(c_36683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34442, c_36681])).
% 14.69/6.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.69/6.07  
% 14.69/6.07  Inference rules
% 14.69/6.07  ----------------------
% 14.69/6.07  #Ref     : 0
% 14.69/6.07  #Sup     : 9687
% 14.69/6.07  #Fact    : 0
% 14.69/6.07  #Define  : 0
% 14.69/6.07  #Split   : 18
% 14.69/6.07  #Chain   : 0
% 14.69/6.07  #Close   : 0
% 14.69/6.07  
% 14.69/6.07  Ordering : KBO
% 14.69/6.07  
% 14.69/6.07  Simplification rules
% 14.69/6.07  ----------------------
% 14.69/6.07  #Subsume      : 4252
% 14.69/6.07  #Demod        : 7085
% 14.69/6.07  #Tautology    : 2216
% 14.69/6.07  #SimpNegUnit  : 777
% 14.69/6.07  #BackRed      : 21
% 14.69/6.07  
% 14.69/6.07  #Partial instantiations: 0
% 14.69/6.07  #Strategies tried      : 1
% 14.69/6.07  
% 14.69/6.07  Timing (in seconds)
% 14.69/6.07  ----------------------
% 14.69/6.07  Preprocessing        : 0.42
% 14.69/6.07  Parsing              : 0.18
% 14.69/6.07  CNF conversion       : 0.04
% 14.69/6.07  Main loop            : 4.88
% 14.69/6.07  Inferencing          : 0.95
% 14.69/6.07  Reduction            : 1.37
% 14.69/6.07  Demodulation         : 0.94
% 14.69/6.07  BG Simplification    : 0.11
% 14.69/6.07  Subsumption          : 2.19
% 14.69/6.07  Abstraction          : 0.17
% 14.69/6.07  MUC search           : 0.00
% 14.69/6.07  Cooper               : 0.00
% 14.69/6.07  Total                : 5.34
% 14.69/6.07  Index Insertion      : 0.00
% 14.69/6.07  Index Deletion       : 0.00
% 14.69/6.07  Index Matching       : 0.00
% 14.69/6.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
