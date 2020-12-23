%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0833+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:55 EST 2020

% Result     : Theorem 12.22s
% Output     : CNFRefutation 12.38s
% Verified   : 
% Statistics : Number of formulae       :  367 (3889 expanded)
%              Number of leaves         :   40 (1217 expanded)
%              Depth                    :   25
%              Number of atoms          :  670 (8341 expanded)
%              Number of equality atoms :  115 ( 854 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_51,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(c_28,plain,(
    ! [A_28] : m1_subset_1('#skF_5'(A_28),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_96,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_109,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_96])).

tff(c_13984,plain,(
    ! [A_1215,B_1216,C_1217,D_1218] :
      ( r2_relset_1(A_1215,B_1216,C_1217,C_1217)
      | ~ m1_subset_1(D_1218,k1_zfmisc_1(k2_zfmisc_1(A_1215,B_1216)))
      | ~ m1_subset_1(C_1217,k1_zfmisc_1(k2_zfmisc_1(A_1215,B_1216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_23622,plain,(
    ! [C_1839] :
      ( r2_relset_1('#skF_6','#skF_7',C_1839,C_1839)
      | ~ m1_subset_1(C_1839,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_13984])).

tff(c_23643,plain,(
    r2_relset_1('#skF_6','#skF_7','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_23622])).

tff(c_58,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_133,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ v1_xboole_0(C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_151,plain,(
    ! [B_85,A_86,A_87] :
      ( ~ v1_xboole_0(B_85)
      | ~ r2_hidden(A_86,A_87)
      | ~ r1_tarski(A_87,B_85) ) ),
    inference(resolution,[status(thm)],[c_46,c_133])).

tff(c_187,plain,(
    ! [B_105,B_106,A_107] :
      ( ~ v1_xboole_0(B_105)
      | ~ r1_tarski(B_106,B_105)
      | v1_xboole_0(B_106)
      | ~ m1_subset_1(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_42,c_151])).

tff(c_196,plain,(
    ! [A_107] :
      ( ~ v1_xboole_0('#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_107,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_197,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_12,plain,(
    ! [A_4,B_5,C_15] :
      ( r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),B_5)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),C_15)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24182,plain,(
    ! [A_1893,B_1894,C_1895] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1893,B_1894,C_1895),'#skF_2'(A_1893,B_1894,C_1895)),C_1895)
      | r2_hidden(k4_tarski('#skF_3'(A_1893,B_1894,C_1895),'#skF_4'(A_1893,B_1894,C_1895)),C_1895)
      | k8_relat_1(A_1893,B_1894) = C_1895
      | ~ v1_relat_1(C_1895)
      | ~ v1_relat_1(B_1894) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27254,plain,(
    ! [A_2094,B_2095] :
      ( r2_hidden(k4_tarski('#skF_3'(A_2094,B_2095,B_2095),'#skF_4'(A_2094,B_2095,B_2095)),B_2095)
      | k8_relat_1(A_2094,B_2095) = B_2095
      | ~ v1_relat_1(B_2095) ) ),
    inference(resolution,[status(thm)],[c_12,c_24182])).

tff(c_142,plain,(
    ! [A_82] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_82,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_144,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_155,plain,(
    ! [A_88,C_89,B_90] :
      ( m1_subset_1(A_88,C_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(C_89))
      | ~ r2_hidden(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,(
    ! [A_88] :
      ( m1_subset_1(A_88,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_88,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_177,plain,(
    ! [B_97,D_98,A_99,C_100] :
      ( r2_hidden(B_97,D_98)
      | ~ r2_hidden(k4_tarski(A_99,B_97),k2_zfmisc_1(C_100,D_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25779,plain,(
    ! [B_1967,D_1968,C_1969,A_1970] :
      ( r2_hidden(B_1967,D_1968)
      | v1_xboole_0(k2_zfmisc_1(C_1969,D_1968))
      | ~ m1_subset_1(k4_tarski(A_1970,B_1967),k2_zfmisc_1(C_1969,D_1968)) ) ),
    inference(resolution,[status(thm)],[c_42,c_177])).

tff(c_25790,plain,(
    ! [B_1967,A_1970] :
      ( r2_hidden(B_1967,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k4_tarski(A_1970,B_1967),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_164,c_25779])).

tff(c_25797,plain,(
    ! [B_1967,A_1970] :
      ( r2_hidden(B_1967,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_1970,B_1967),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_25790])).

tff(c_27270,plain,(
    ! [A_2094] :
      ( r2_hidden('#skF_4'(A_2094,'#skF_9','#skF_9'),'#skF_7')
      | k8_relat_1(A_2094,'#skF_9') = '#skF_9'
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_27254,c_25797])).

tff(c_27486,plain,(
    ! [A_2102] :
      ( r2_hidden('#skF_4'(A_2102,'#skF_9','#skF_9'),'#skF_7')
      | k8_relat_1(A_2102,'#skF_9') = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_27270])).

tff(c_40,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_27527,plain,(
    ! [A_2107] :
      ( m1_subset_1('#skF_4'(A_2107,'#skF_9','#skF_9'),'#skF_7')
      | k8_relat_1(A_2107,'#skF_9') = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_27486,c_40])).

tff(c_110,plain,(
    ! [A_71,B_72] : v1_relat_1('#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))) ),
    inference(resolution,[status(thm)],[c_28,c_96])).

tff(c_14269,plain,(
    ! [A_1237,B_1238,C_1239] :
      ( r2_hidden('#skF_2'(A_1237,B_1238,C_1239),A_1237)
      | r2_hidden(k4_tarski('#skF_3'(A_1237,B_1238,C_1239),'#skF_4'(A_1237,B_1238,C_1239)),C_1239)
      | k8_relat_1(A_1237,B_1238) = C_1239
      | ~ v1_relat_1(C_1239)
      | ~ v1_relat_1(B_1238) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_93,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_81])).

tff(c_173,plain,(
    ! [A_94,B_95,A_96] :
      ( m1_subset_1(A_94,B_95)
      | ~ r2_hidden(A_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(resolution,[status(thm)],[c_46,c_155])).

tff(c_13967,plain,(
    ! [A_1212,B_1213,B_1214] :
      ( m1_subset_1(A_1212,B_1213)
      | ~ r1_tarski(B_1214,B_1213)
      | v1_xboole_0(B_1214)
      | ~ m1_subset_1(A_1212,B_1214) ) ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_13982,plain,(
    ! [A_1212] :
      ( m1_subset_1(A_1212,k2_zfmisc_1('#skF_6','#skF_7'))
      | v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_1212,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_93,c_13967])).

tff(c_14159,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_13982])).

tff(c_13983,plain,(
    ! [A_1212] :
      ( m1_subset_1(A_1212,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_1212,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_13967])).

tff(c_14005,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_13983])).

tff(c_52,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14009,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_14005,c_52])).

tff(c_14017,plain,(
    ! [A_54] :
      ( A_54 = '#skF_7'
      | ~ v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14009,c_52])).

tff(c_14163,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14159,c_14017])).

tff(c_145,plain,(
    ! [C_83,A_84] :
      ( ~ v1_xboole_0(C_83)
      | ~ r2_hidden(A_84,'#skF_5'(k1_zfmisc_1(C_83))) ) ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_198,plain,(
    ! [C_108,A_109] :
      ( ~ v1_xboole_0(C_108)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_108)))
      | ~ m1_subset_1(A_109,'#skF_5'(k1_zfmisc_1(C_108))) ) ),
    inference(resolution,[status(thm)],[c_42,c_145])).

tff(c_226,plain,(
    ! [C_114] :
      ( ~ v1_xboole_0(C_114)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_114))) ) ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_231,plain,(
    ! [C_115] :
      ( '#skF_5'(k1_zfmisc_1(C_115)) = k1_xboole_0
      | ~ v1_xboole_0(C_115) ) ),
    inference(resolution,[status(thm)],[c_226,c_52])).

tff(c_281,plain,(
    ! [C_121] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_121))
      | ~ v1_xboole_0(C_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_28])).

tff(c_50,plain,(
    ! [C_53,B_52,A_51] :
      ( ~ v1_xboole_0(C_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_53))
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_298,plain,(
    ! [A_51,C_121] :
      ( ~ r2_hidden(A_51,k1_xboole_0)
      | ~ v1_xboole_0(C_121) ) ),
    inference(resolution,[status(thm)],[c_281,c_50])).

tff(c_301,plain,(
    ! [C_121] : ~ v1_xboole_0(C_121) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_26,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_61])).

tff(c_66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_26])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_66])).

tff(c_307,plain,(
    ! [A_51] : ~ r2_hidden(A_51,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_14011,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14009,c_307])).

tff(c_14201,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14163,c_14011])).

tff(c_14273,plain,(
    ! [A_1237,B_1238] :
      ( r2_hidden('#skF_2'(A_1237,B_1238,'#skF_9'),A_1237)
      | k8_relat_1(A_1237,B_1238) = '#skF_9'
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(B_1238) ) ),
    inference(resolution,[status(thm)],[c_14269,c_14201])).

tff(c_15067,plain,(
    ! [A_1313,B_1314] :
      ( r2_hidden('#skF_2'(A_1313,B_1314,'#skF_9'),A_1313)
      | k8_relat_1(A_1313,B_1314) = '#skF_9'
      | ~ v1_relat_1(B_1314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_14273])).

tff(c_15107,plain,(
    ! [B_1315] :
      ( k8_relat_1('#skF_9',B_1315) = '#skF_9'
      | ~ v1_relat_1(B_1315) ) ),
    inference(resolution,[status(thm)],[c_15067,c_14201])).

tff(c_15133,plain,(
    ! [A_71,B_72] : k8_relat_1('#skF_9','#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_110,c_15107])).

tff(c_269,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k6_relset_1(A_117,B_118,C_119,D_120) = k8_relat_1(C_119,D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_17015,plain,(
    ! [A_1429,B_1430,C_1431] : k6_relset_1(A_1429,B_1430,C_1431,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_1429,B_1430)))) = k8_relat_1(C_1431,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_1429,B_1430)))) ),
    inference(resolution,[status(thm)],[c_28,c_269])).

tff(c_13910,plain,(
    ! [A_1203,B_1204,C_1205,D_1206] :
      ( m1_subset_1(k6_relset_1(A_1203,B_1204,C_1205,D_1206),k1_zfmisc_1(k2_zfmisc_1(A_1203,B_1204)))
      | ~ m1_subset_1(D_1206,k1_zfmisc_1(k2_zfmisc_1(A_1203,B_1204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_13930,plain,(
    ! [A_1203,B_1204,C_1205,D_1206] :
      ( r1_tarski(k6_relset_1(A_1203,B_1204,C_1205,D_1206),k2_zfmisc_1(A_1203,B_1204))
      | ~ m1_subset_1(D_1206,k1_zfmisc_1(k2_zfmisc_1(A_1203,B_1204))) ) ),
    inference(resolution,[status(thm)],[c_13910,c_44])).

tff(c_17025,plain,(
    ! [C_1431,A_1429,B_1430] :
      ( r1_tarski(k8_relat_1(C_1431,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_1429,B_1430)))),k2_zfmisc_1(A_1429,B_1430))
      | ~ m1_subset_1('#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_1429,B_1430))),k1_zfmisc_1(k2_zfmisc_1(A_1429,B_1430))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17015,c_13930])).

tff(c_17215,plain,(
    ! [C_1439,A_1440,B_1441] : r1_tarski(k8_relat_1(C_1439,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_1440,B_1441)))),k2_zfmisc_1(A_1440,B_1441)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_17025])).

tff(c_17259,plain,(
    ! [A_1442,B_1443] : r1_tarski('#skF_9',k2_zfmisc_1(A_1442,B_1443)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15133,c_17215])).

tff(c_14661,plain,(
    ! [A_1257,B_1258,C_1259] :
      ( r2_relset_1(A_1257,B_1258,C_1259,C_1259)
      | ~ m1_subset_1(C_1259,k1_zfmisc_1(k2_zfmisc_1(A_1257,B_1258))) ) ),
    inference(resolution,[status(thm)],[c_28,c_13984])).

tff(c_14683,plain,(
    ! [A_1257,B_1258,A_46] :
      ( r2_relset_1(A_1257,B_1258,A_46,A_46)
      | ~ r1_tarski(A_46,k2_zfmisc_1(A_1257,B_1258)) ) ),
    inference(resolution,[status(thm)],[c_46,c_14661])).

tff(c_17278,plain,(
    ! [A_1442,B_1443] : r2_relset_1(A_1442,B_1443,'#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_17259,c_14683])).

tff(c_14544,plain,(
    ! [A_1254,B_1255,C_1256] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1254,B_1255,C_1256),'#skF_2'(A_1254,B_1255,C_1256)),B_1255)
      | r2_hidden(k4_tarski('#skF_3'(A_1254,B_1255,C_1256),'#skF_4'(A_1254,B_1255,C_1256)),C_1256)
      | k8_relat_1(A_1254,B_1255) = C_1256
      | ~ v1_relat_1(C_1256)
      | ~ v1_relat_1(B_1255) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_4,B_5,C_15] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),C_15)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),C_15)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17537,plain,(
    ! [A_1464,B_1465] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1464,B_1465,B_1465),'#skF_4'(A_1464,B_1465,B_1465)),B_1465)
      | k8_relat_1(A_1464,B_1465) = B_1465
      | ~ v1_relat_1(B_1465) ) ),
    inference(resolution,[status(thm)],[c_14544,c_10])).

tff(c_17563,plain,(
    ! [A_1464] :
      ( k8_relat_1(A_1464,'#skF_9') = '#skF_9'
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_17537,c_14201])).

tff(c_17612,plain,(
    ! [A_1464] : k8_relat_1(A_1464,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_17563])).

tff(c_279,plain,(
    ! [C_119] : k6_relset_1('#skF_6','#skF_7',C_119,'#skF_9') = k8_relat_1(C_119,'#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_269])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_6','#skF_7',k6_relset_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_13892,plain,(
    ~ r2_relset_1('#skF_6','#skF_7',k8_relat_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_56])).

tff(c_14210,plain,(
    ~ r2_relset_1('#skF_6','#skF_9',k8_relat_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14163,c_13892])).

tff(c_17652,plain,(
    ~ r2_relset_1('#skF_6','#skF_9','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17612,c_14210])).

tff(c_17673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17278,c_17652])).

tff(c_17675,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_13982])).

tff(c_14,plain,(
    ! [A_4,B_5,C_15] :
      ( r2_hidden('#skF_2'(A_4,B_5,C_15),A_4)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),C_15)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_19967,plain,(
    ! [B_1604,D_1605,C_1606,A_1607] :
      ( r2_hidden(B_1604,D_1605)
      | v1_xboole_0(k2_zfmisc_1(C_1606,D_1605))
      | ~ m1_subset_1(k4_tarski(A_1607,B_1604),k2_zfmisc_1(C_1606,D_1605)) ) ),
    inference(resolution,[status(thm)],[c_42,c_177])).

tff(c_19978,plain,(
    ! [B_1604,A_1607] :
      ( r2_hidden(B_1604,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k4_tarski(A_1607,B_1604),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_164,c_19967])).

tff(c_19986,plain,(
    ! [A_1608,B_1609] : ~ r2_hidden(k4_tarski(A_1608,B_1609),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_14011,c_19978])).

tff(c_20000,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_2'(A_4,B_5,'#skF_9'),A_4)
      | k8_relat_1(A_4,B_5) = '#skF_9'
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_19986])).

tff(c_20018,plain,(
    ! [A_1612,B_1613] :
      ( r2_hidden('#skF_2'(A_1612,B_1613,'#skF_9'),A_1612)
      | k8_relat_1(A_1612,B_1613) = '#skF_9'
      | ~ v1_relat_1(B_1613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_20000])).

tff(c_20063,plain,(
    ! [B_1614] :
      ( k8_relat_1('#skF_7',B_1614) = '#skF_9'
      | ~ v1_relat_1(B_1614) ) ),
    inference(resolution,[status(thm)],[c_20018,c_14011])).

tff(c_20106,plain,(
    k8_relat_1('#skF_7','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_109,c_20063])).

tff(c_9713,plain,(
    ! [A_800,B_801,C_802,D_803] :
      ( r2_relset_1(A_800,B_801,C_802,C_802)
      | ~ m1_subset_1(D_803,k1_zfmisc_1(k2_zfmisc_1(A_800,B_801)))
      | ~ m1_subset_1(C_802,k1_zfmisc_1(k2_zfmisc_1(A_800,B_801))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9734,plain,(
    ! [C_804] :
      ( r2_relset_1('#skF_6','#skF_7',C_804,C_804)
      | ~ m1_subset_1(C_804,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_9713])).

tff(c_9755,plain,(
    r2_relset_1('#skF_6','#skF_7','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_9734])).

tff(c_10411,plain,(
    ! [A_882,B_883,C_884] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_882,B_883,C_884),'#skF_2'(A_882,B_883,C_884)),C_884)
      | r2_hidden(k4_tarski('#skF_3'(A_882,B_883,C_884),'#skF_4'(A_882,B_883,C_884)),C_884)
      | k8_relat_1(A_882,B_883) = C_884
      | ~ v1_relat_1(C_884)
      | ~ v1_relat_1(B_883) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11414,plain,(
    ! [A_1001,B_1002] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1001,B_1002,B_1002),'#skF_4'(A_1001,B_1002,B_1002)),B_1002)
      | k8_relat_1(A_1001,B_1002) = B_1002
      | ~ v1_relat_1(B_1002) ) ),
    inference(resolution,[status(thm)],[c_12,c_10411])).

tff(c_246,plain,(
    ! [A_71,B_72] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(k2_zfmisc_1(A_71,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_110])).

tff(c_315,plain,(
    ! [A_71,B_72] : ~ v1_xboole_0(k2_zfmisc_1(A_71,B_72)) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_181,plain,(
    ! [B_97,D_98,C_100,A_99] :
      ( r2_hidden(B_97,D_98)
      | v1_xboole_0(k2_zfmisc_1(C_100,D_98))
      | ~ m1_subset_1(k4_tarski(A_99,B_97),k2_zfmisc_1(C_100,D_98)) ) ),
    inference(resolution,[status(thm)],[c_42,c_177])).

tff(c_10361,plain,(
    ! [B_872,D_873,A_874,C_875] :
      ( r2_hidden(B_872,D_873)
      | ~ m1_subset_1(k4_tarski(A_874,B_872),k2_zfmisc_1(C_875,D_873)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_181])).

tff(c_10375,plain,(
    ! [B_872,A_874] :
      ( r2_hidden(B_872,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_874,B_872),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_164,c_10361])).

tff(c_11433,plain,(
    ! [A_1001] :
      ( r2_hidden('#skF_4'(A_1001,'#skF_9','#skF_9'),'#skF_7')
      | k8_relat_1(A_1001,'#skF_9') = '#skF_9'
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_11414,c_10375])).

tff(c_11535,plain,(
    ! [A_1006] :
      ( r2_hidden('#skF_4'(A_1006,'#skF_9','#skF_9'),'#skF_7')
      | k8_relat_1(A_1006,'#skF_9') = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_11433])).

tff(c_11552,plain,(
    ! [A_1010] :
      ( m1_subset_1('#skF_4'(A_1010,'#skF_9','#skF_9'),'#skF_7')
      | k8_relat_1(A_1010,'#skF_9') = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_11535,c_40])).

tff(c_389,plain,(
    ! [A_139,B_140,B_141] :
      ( m1_subset_1(A_139,B_140)
      | ~ r1_tarski(B_141,B_140)
      | v1_xboole_0(B_141)
      | ~ m1_subset_1(A_139,B_141) ) ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_405,plain,(
    ! [A_139] :
      ( m1_subset_1(A_139,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_139,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_389])).

tff(c_406,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_410,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_406,c_52])).

tff(c_411,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_307])).

tff(c_4630,plain,(
    ! [B_462,D_463,A_464,C_465] :
      ( r2_hidden(B_462,D_463)
      | ~ m1_subset_1(k4_tarski(A_464,B_462),k2_zfmisc_1(C_465,D_463)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_181])).

tff(c_4641,plain,(
    ! [B_462,A_464] :
      ( r2_hidden(B_462,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_464,B_462),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_164,c_4630])).

tff(c_4649,plain,(
    ! [A_466,B_467] : ~ r2_hidden(k4_tarski(A_466,B_467),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_4641])).

tff(c_4659,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_2'(A_4,B_5,'#skF_9'),A_4)
      | k8_relat_1(A_4,B_5) = '#skF_9'
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_4649])).

tff(c_4673,plain,(
    ! [A_470,B_471] :
      ( r2_hidden('#skF_2'(A_470,B_471,'#skF_9'),A_470)
      | k8_relat_1(A_470,B_471) = '#skF_9'
      | ~ v1_relat_1(B_471) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_4659])).

tff(c_4713,plain,(
    ! [B_472] :
      ( k8_relat_1('#skF_7',B_472) = '#skF_9'
      | ~ v1_relat_1(B_472) ) ),
    inference(resolution,[status(thm)],[c_4673,c_411])).

tff(c_4739,plain,(
    ! [A_71,B_72] : k8_relat_1('#skF_7','#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_110,c_4713])).

tff(c_6167,plain,(
    ! [A_532,B_533,C_534] : k6_relset_1(A_532,B_533,C_534,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_532,B_533)))) = k8_relat_1(C_534,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_532,B_533)))) ),
    inference(resolution,[status(thm)],[c_28,c_269])).

tff(c_332,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( m1_subset_1(k6_relset_1(A_130,B_131,C_132,D_133),k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_352,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( r1_tarski(k6_relset_1(A_130,B_131,C_132,D_133),k2_zfmisc_1(A_130,B_131))
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(resolution,[status(thm)],[c_332,c_44])).

tff(c_6173,plain,(
    ! [C_534,A_532,B_533] :
      ( r1_tarski(k8_relat_1(C_534,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_532,B_533)))),k2_zfmisc_1(A_532,B_533))
      | ~ m1_subset_1('#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_532,B_533))),k1_zfmisc_1(k2_zfmisc_1(A_532,B_533))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6167,c_352])).

tff(c_6307,plain,(
    ! [C_542,A_543,B_544] : r1_tarski(k8_relat_1(C_542,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_543,B_544)))),k2_zfmisc_1(A_543,B_544)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6173])).

tff(c_6344,plain,(
    ! [A_545,B_546] : r1_tarski('#skF_9',k2_zfmisc_1(A_545,B_546)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4739,c_6307])).

tff(c_427,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( r2_relset_1(A_142,B_143,C_144,C_144)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3974,plain,(
    ! [A_377,B_378,C_379] :
      ( r2_relset_1(A_377,B_378,C_379,C_379)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378))) ) ),
    inference(resolution,[status(thm)],[c_28,c_427])).

tff(c_3994,plain,(
    ! [A_377,B_378,A_46] :
      ( r2_relset_1(A_377,B_378,A_46,A_46)
      | ~ r1_tarski(A_46,k2_zfmisc_1(A_377,B_378)) ) ),
    inference(resolution,[status(thm)],[c_46,c_3974])).

tff(c_6363,plain,(
    ! [A_545,B_546] : r2_relset_1(A_545,B_546,'#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_6344,c_3994])).

tff(c_4394,plain,(
    ! [A_447,B_448,C_449] :
      ( r2_hidden(k4_tarski('#skF_1'(A_447,B_448,C_449),'#skF_2'(A_447,B_448,C_449)),B_448)
      | r2_hidden(k4_tarski('#skF_3'(A_447,B_448,C_449),'#skF_4'(A_447,B_448,C_449)),C_449)
      | k8_relat_1(A_447,B_448) = C_449
      | ~ v1_relat_1(C_449)
      | ~ v1_relat_1(B_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6553,plain,(
    ! [A_571,B_572] :
      ( r2_hidden(k4_tarski('#skF_3'(A_571,B_572,B_572),'#skF_4'(A_571,B_572,B_572)),B_572)
      | k8_relat_1(A_571,B_572) = B_572
      | ~ v1_relat_1(B_572) ) ),
    inference(resolution,[status(thm)],[c_4394,c_10])).

tff(c_4648,plain,(
    ! [A_464,B_462] : ~ r2_hidden(k4_tarski(A_464,B_462),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_4641])).

tff(c_6565,plain,(
    ! [A_571] :
      ( k8_relat_1(A_571,'#skF_9') = '#skF_9'
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6553,c_4648])).

tff(c_6621,plain,(
    ! [A_571] : k8_relat_1(A_571,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_6565])).

tff(c_322,plain,(
    ~ r2_relset_1('#skF_6','#skF_7',k8_relat_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_56])).

tff(c_6671,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6621,c_322])).

tff(c_6689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6363,c_6671])).

tff(c_6690,plain,(
    ! [A_139] :
      ( m1_subset_1(A_139,'#skF_8')
      | ~ m1_subset_1(A_139,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_11556,plain,(
    ! [A_1010] :
      ( m1_subset_1('#skF_4'(A_1010,'#skF_9','#skF_9'),'#skF_8')
      | k8_relat_1(A_1010,'#skF_9') = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_11552,c_6690])).

tff(c_10428,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(k4_tarski('#skF_3'(A_4,B_5,B_5),'#skF_4'(A_4,B_5,B_5)),B_5)
      | k8_relat_1(A_4,B_5) = B_5
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_10411])).

tff(c_6,plain,(
    ! [A_4,B_5,C_15] :
      ( r2_hidden(k4_tarski('#skF_1'(A_4,B_5,C_15),'#skF_2'(A_4,B_5,C_15)),B_5)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_4,B_5,C_15),'#skF_4'(A_4,B_5,C_15)),B_5)
      | ~ r2_hidden('#skF_4'(A_4,B_5,C_15),A_4)
      | k8_relat_1(A_4,B_5) = C_15
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10916,plain,(
    ! [A_926,B_927,C_928] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_926,B_927,C_928),'#skF_2'(A_926,B_927,C_928)),C_928)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_926,B_927,C_928),'#skF_4'(A_926,B_927,C_928)),B_927)
      | ~ r2_hidden('#skF_4'(A_926,B_927,C_928),A_926)
      | k8_relat_1(A_926,B_927) = C_928
      | ~ v1_relat_1(C_928)
      | ~ v1_relat_1(B_927) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13704,plain,(
    ! [A_1188,B_1189] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_1188,B_1189,B_1189),'#skF_4'(A_1188,B_1189,B_1189)),B_1189)
      | ~ r2_hidden('#skF_4'(A_1188,B_1189,B_1189),A_1188)
      | k8_relat_1(A_1188,B_1189) = B_1189
      | ~ v1_relat_1(B_1189) ) ),
    inference(resolution,[status(thm)],[c_6,c_10916])).

tff(c_13757,plain,(
    ! [A_1190,B_1191] :
      ( ~ r2_hidden('#skF_4'(A_1190,B_1191,B_1191),A_1190)
      | k8_relat_1(A_1190,B_1191) = B_1191
      | ~ v1_relat_1(B_1191) ) ),
    inference(resolution,[status(thm)],[c_10428,c_13704])).

tff(c_13791,plain,(
    ! [B_1192,B_1193] :
      ( k8_relat_1(B_1192,B_1193) = B_1193
      | ~ v1_relat_1(B_1193)
      | v1_xboole_0(B_1192)
      | ~ m1_subset_1('#skF_4'(B_1192,B_1193,B_1193),B_1192) ) ),
    inference(resolution,[status(thm)],[c_42,c_13757])).

tff(c_13819,plain,
    ( ~ v1_relat_1('#skF_9')
    | v1_xboole_0('#skF_8')
    | k8_relat_1('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_11556,c_13791])).

tff(c_13866,plain,
    ( v1_xboole_0('#skF_8')
    | k8_relat_1('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_13819])).

tff(c_13867,plain,(
    k8_relat_1('#skF_8','#skF_9') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_13866])).

tff(c_13887,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13867,c_322])).

tff(c_13890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9755,c_13887])).

tff(c_13891,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_14010,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14009,c_13891])).

tff(c_17861,plain,(
    ! [A_1500,B_1501,C_1502] :
      ( r2_hidden('#skF_2'(A_1500,B_1501,C_1502),A_1500)
      | r2_hidden(k4_tarski('#skF_3'(A_1500,B_1501,C_1502),'#skF_4'(A_1500,B_1501,C_1502)),C_1502)
      | k8_relat_1(A_1500,B_1501) = C_1502
      | ~ v1_relat_1(C_1502)
      | ~ v1_relat_1(B_1501) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17869,plain,(
    ! [A_1500,B_1501] :
      ( r2_hidden('#skF_2'(A_1500,B_1501,'#skF_7'),A_1500)
      | k8_relat_1(A_1500,B_1501) = '#skF_7'
      | ~ v1_relat_1('#skF_7')
      | ~ v1_relat_1(B_1501) ) ),
    inference(resolution,[status(thm)],[c_17861,c_14011])).

tff(c_18164,plain,(
    ! [A_1526,B_1527] :
      ( r2_hidden('#skF_2'(A_1526,B_1527,'#skF_7'),A_1526)
      | k8_relat_1(A_1526,B_1527) = '#skF_7'
      | ~ v1_relat_1(B_1527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14010,c_17869])).

tff(c_18204,plain,(
    ! [B_1528] :
      ( k8_relat_1('#skF_7',B_1528) = '#skF_7'
      | ~ v1_relat_1(B_1528) ) ),
    inference(resolution,[status(thm)],[c_18164,c_14011])).

tff(c_18235,plain,(
    k8_relat_1('#skF_7','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_109,c_18204])).

tff(c_20108,plain,(
    '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20106,c_18235])).

tff(c_20254,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20108,c_14005])).

tff(c_20269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17675,c_20254])).

tff(c_20270,plain,(
    ! [A_1212] :
      ( m1_subset_1(A_1212,'#skF_8')
      | ~ m1_subset_1(A_1212,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_13983])).

tff(c_27531,plain,(
    ! [A_2107] :
      ( m1_subset_1('#skF_4'(A_2107,'#skF_9','#skF_9'),'#skF_8')
      | k8_relat_1(A_2107,'#skF_9') = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_27527,c_20270])).

tff(c_24199,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(k4_tarski('#skF_3'(A_4,B_5,B_5),'#skF_4'(A_4,B_5,B_5)),B_5)
      | k8_relat_1(A_4,B_5) = B_5
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_24182])).

tff(c_24954,plain,(
    ! [A_1930,B_1931,C_1932] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1930,B_1931,C_1932),'#skF_2'(A_1930,B_1931,C_1932)),C_1932)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1930,B_1931,C_1932),'#skF_4'(A_1930,B_1931,C_1932)),B_1931)
      | ~ r2_hidden('#skF_4'(A_1930,B_1931,C_1932),A_1930)
      | k8_relat_1(A_1930,B_1931) = C_1932
      | ~ v1_relat_1(C_1932)
      | ~ v1_relat_1(B_1931) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32781,plain,(
    ! [A_2272,B_2273] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_2272,B_2273,B_2273),'#skF_4'(A_2272,B_2273,B_2273)),B_2273)
      | ~ r2_hidden('#skF_4'(A_2272,B_2273,B_2273),A_2272)
      | k8_relat_1(A_2272,B_2273) = B_2273
      | ~ v1_relat_1(B_2273) ) ),
    inference(resolution,[status(thm)],[c_6,c_24954])).

tff(c_33151,plain,(
    ! [A_2278,B_2279] :
      ( ~ r2_hidden('#skF_4'(A_2278,B_2279,B_2279),A_2278)
      | k8_relat_1(A_2278,B_2279) = B_2279
      | ~ v1_relat_1(B_2279) ) ),
    inference(resolution,[status(thm)],[c_24199,c_32781])).

tff(c_36684,plain,(
    ! [B_2330,B_2331] :
      ( k8_relat_1(B_2330,B_2331) = B_2331
      | ~ v1_relat_1(B_2331)
      | v1_xboole_0(B_2330)
      | ~ m1_subset_1('#skF_4'(B_2330,B_2331,B_2331),B_2330) ) ),
    inference(resolution,[status(thm)],[c_42,c_33151])).

tff(c_36692,plain,
    ( ~ v1_relat_1('#skF_9')
    | v1_xboole_0('#skF_8')
    | k8_relat_1('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_27531,c_36684])).

tff(c_36714,plain,
    ( v1_xboole_0('#skF_8')
    | k8_relat_1('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_36692])).

tff(c_36715,plain,(
    k8_relat_1('#skF_8','#skF_9') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_36714])).

tff(c_36727,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36715,c_13892])).

tff(c_36730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23643,c_36727])).

tff(c_36731,plain,(
    ! [A_107] :
      ( ~ m1_subset_1(A_107,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_36779,plain,(
    ! [A_2337] : ~ m1_subset_1(A_2337,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_36731])).

tff(c_36784,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28,c_36779])).

tff(c_36785,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_36731])).

tff(c_36732,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_36736,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_36732,c_52])).

tff(c_36739,plain,(
    ! [A_54] :
      ( A_54 = '#skF_8'
      | ~ v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36736,c_52])).

tff(c_36789,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_36785,c_36739])).

tff(c_36795,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36789,c_60])).

tff(c_37713,plain,(
    ! [A_2461,B_2462,C_2463,D_2464] :
      ( r2_relset_1(A_2461,B_2462,C_2463,C_2463)
      | ~ m1_subset_1(D_2464,k1_zfmisc_1(k2_zfmisc_1(A_2461,B_2462)))
      | ~ m1_subset_1(C_2463,k1_zfmisc_1(k2_zfmisc_1(A_2461,B_2462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37755,plain,(
    ! [C_2467] :
      ( r2_relset_1('#skF_6','#skF_8',C_2467,C_2467)
      | ~ m1_subset_1(C_2467,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_36795,c_37713])).

tff(c_37778,plain,(
    r2_relset_1('#skF_6','#skF_8','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_36795,c_37755])).

tff(c_37605,plain,(
    ! [C_2446,A_2447] :
      ( ~ v1_xboole_0(C_2446)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_2446)))
      | ~ m1_subset_1(A_2447,'#skF_5'(k1_zfmisc_1(C_2446))) ) ),
    inference(resolution,[status(thm)],[c_42,c_145])).

tff(c_37610,plain,(
    ! [C_2448] :
      ( ~ v1_xboole_0(C_2448)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_2448))) ) ),
    inference(resolution,[status(thm)],[c_28,c_37605])).

tff(c_37615,plain,(
    ! [C_2449] :
      ( '#skF_5'(k1_zfmisc_1(C_2449)) = '#skF_8'
      | ~ v1_xboole_0(C_2449) ) ),
    inference(resolution,[status(thm)],[c_37610,c_36739])).

tff(c_37664,plain,(
    ! [C_2457] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(C_2457))
      | ~ v1_xboole_0(C_2457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37615,c_28])).

tff(c_37681,plain,(
    ! [A_51,C_2457] :
      ( ~ r2_hidden(A_51,'#skF_8')
      | ~ v1_xboole_0(C_2457) ) ),
    inference(resolution,[status(thm)],[c_37664,c_50])).

tff(c_37698,plain,(
    ! [C_2457] : ~ v1_xboole_0(C_2457) ),
    inference(splitLeft,[status(thm)],[c_37681])).

tff(c_37704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37698,c_36732])).

tff(c_37705,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_37681])).

tff(c_36791,plain,(
    ! [A_88] :
      ( m1_subset_1(A_88,k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(A_88,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36789,c_164])).

tff(c_37630,plain,(
    ! [A_71,B_72] :
      ( v1_relat_1('#skF_8')
      | ~ v1_xboole_0(k2_zfmisc_1(A_71,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37615,c_110])).

tff(c_37662,plain,(
    ! [A_71,B_72] : ~ v1_xboole_0(k2_zfmisc_1(A_71,B_72)) ),
    inference(splitLeft,[status(thm)],[c_37630])).

tff(c_38167,plain,(
    ! [B_2531,D_2532,A_2533,C_2534] :
      ( r2_hidden(B_2531,D_2532)
      | ~ m1_subset_1(k4_tarski(A_2533,B_2531),k2_zfmisc_1(C_2534,D_2532)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37662,c_181])).

tff(c_38178,plain,(
    ! [B_2531,A_2533] :
      ( r2_hidden(B_2531,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_2533,B_2531),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36791,c_38167])).

tff(c_38202,plain,(
    ! [A_2538,B_2539] : ~ r2_hidden(k4_tarski(A_2538,B_2539),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_37705,c_38178])).

tff(c_38206,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_2'(A_4,B_5,'#skF_9'),A_4)
      | k8_relat_1(A_4,B_5) = '#skF_9'
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_38202])).

tff(c_38217,plain,(
    ! [A_2542,B_2543] :
      ( r2_hidden('#skF_2'(A_2542,B_2543,'#skF_9'),A_2542)
      | k8_relat_1(A_2542,B_2543) = '#skF_9'
      | ~ v1_relat_1(B_2543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_38206])).

tff(c_38257,plain,(
    ! [B_2544] :
      ( k8_relat_1('#skF_8',B_2544) = '#skF_9'
      | ~ v1_relat_1(B_2544) ) ),
    inference(resolution,[status(thm)],[c_38217,c_37705])).

tff(c_38284,plain,(
    k8_relat_1('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_109,c_38257])).

tff(c_36831,plain,(
    ! [A_2338,B_2339,C_2340,D_2341] :
      ( k6_relset_1(A_2338,B_2339,C_2340,D_2341) = k8_relat_1(C_2340,D_2341)
      | ~ m1_subset_1(D_2341,k1_zfmisc_1(k2_zfmisc_1(A_2338,B_2339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36840,plain,(
    ! [C_2340] : k6_relset_1('#skF_6','#skF_8',C_2340,'#skF_9') = k8_relat_1(C_2340,'#skF_9') ),
    inference(resolution,[status(thm)],[c_36795,c_36831])).

tff(c_36793,plain,(
    ~ r2_relset_1('#skF_6','#skF_8',k6_relset_1('#skF_6','#skF_8','#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36789,c_36789,c_56])).

tff(c_36853,plain,(
    ~ r2_relset_1('#skF_6','#skF_8',k8_relat_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36840,c_36793])).

tff(c_38286,plain,(
    ~ r2_relset_1('#skF_6','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38284,c_36853])).

tff(c_38289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37778,c_38286])).

tff(c_38290,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_37630])).

tff(c_38677,plain,(
    ! [A_2618,B_2619,C_2620] :
      ( r2_hidden('#skF_2'(A_2618,B_2619,C_2620),A_2618)
      | r2_hidden(k4_tarski('#skF_3'(A_2618,B_2619,C_2620),'#skF_4'(A_2618,B_2619,C_2620)),C_2620)
      | k8_relat_1(A_2618,B_2619) = C_2620
      | ~ v1_relat_1(C_2620)
      | ~ v1_relat_1(B_2619) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38291,plain,(
    ! [C_2545] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(C_2545))
      | ~ v1_xboole_0(C_2545) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37615,c_28])).

tff(c_38308,plain,(
    ! [A_51,C_2545] :
      ( ~ r2_hidden(A_51,'#skF_8')
      | ~ v1_xboole_0(C_2545) ) ),
    inference(resolution,[status(thm)],[c_38291,c_50])).

tff(c_38312,plain,(
    ! [C_2545] : ~ v1_xboole_0(C_2545) ),
    inference(splitLeft,[status(thm)],[c_38308])).

tff(c_38339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38312,c_36732])).

tff(c_38340,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_38308])).

tff(c_38689,plain,(
    ! [A_2618,B_2619] :
      ( r2_hidden('#skF_2'(A_2618,B_2619,'#skF_8'),A_2618)
      | k8_relat_1(A_2618,B_2619) = '#skF_8'
      | ~ v1_relat_1('#skF_8')
      | ~ v1_relat_1(B_2619) ) ),
    inference(resolution,[status(thm)],[c_38677,c_38340])).

tff(c_38743,plain,(
    ! [A_2621,B_2622] :
      ( r2_hidden('#skF_2'(A_2621,B_2622,'#skF_8'),A_2621)
      | k8_relat_1(A_2621,B_2622) = '#skF_8'
      | ~ v1_relat_1(B_2622) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38290,c_38689])).

tff(c_38783,plain,(
    ! [B_2623] :
      ( k8_relat_1('#skF_8',B_2623) = '#skF_8'
      | ~ v1_relat_1(B_2623) ) ),
    inference(resolution,[status(thm)],[c_38743,c_38340])).

tff(c_38814,plain,(
    k8_relat_1('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_109,c_38783])).

tff(c_37544,plain,(
    ! [A_2436,B_2437,C_2438,D_2439] :
      ( m1_subset_1(k6_relset_1(A_2436,B_2437,C_2438,D_2439),k1_zfmisc_1(k2_zfmisc_1(A_2436,B_2437)))
      | ~ m1_subset_1(D_2439,k1_zfmisc_1(k2_zfmisc_1(A_2436,B_2437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37559,plain,(
    ! [C_2340] :
      ( m1_subset_1(k8_relat_1(C_2340,'#skF_9'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36840,c_37544])).

tff(c_37566,plain,(
    ! [C_2340] : m1_subset_1(k8_relat_1(C_2340,'#skF_9'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36795,c_37559])).

tff(c_38382,plain,(
    ! [A_2557,B_2558,C_2559,D_2560] :
      ( r2_relset_1(A_2557,B_2558,C_2559,C_2559)
      | ~ m1_subset_1(D_2560,k1_zfmisc_1(k2_zfmisc_1(A_2557,B_2558)))
      | ~ m1_subset_1(C_2559,k1_zfmisc_1(k2_zfmisc_1(A_2557,B_2558))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38418,plain,(
    ! [A_2563,B_2564,C_2565] :
      ( r2_relset_1(A_2563,B_2564,C_2565,C_2565)
      | ~ m1_subset_1(C_2565,k1_zfmisc_1(k2_zfmisc_1(A_2563,B_2564))) ) ),
    inference(resolution,[status(thm)],[c_28,c_38382])).

tff(c_38438,plain,(
    ! [C_2340] : r2_relset_1('#skF_6','#skF_8',k8_relat_1(C_2340,'#skF_9'),k8_relat_1(C_2340,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_37566,c_38418])).

tff(c_38866,plain,(
    r2_relset_1('#skF_6','#skF_8',k8_relat_1('#skF_8','#skF_9'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_38814,c_38438])).

tff(c_38900,plain,(
    r2_relset_1('#skF_6','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38814,c_38866])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_38470,plain,(
    ! [A_2576,B_2577,C_2578,D_2579] :
      ( v1_relat_1(k6_relset_1(A_2576,B_2577,C_2578,D_2579))
      | ~ m1_subset_1(D_2579,k1_zfmisc_1(k2_zfmisc_1(A_2576,B_2577))) ) ),
    inference(resolution,[status(thm)],[c_37544,c_2])).

tff(c_38496,plain,(
    ! [A_2576,B_2577,C_2578] : v1_relat_1(k6_relset_1(A_2576,B_2577,C_2578,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_2576,B_2577))))) ),
    inference(resolution,[status(thm)],[c_28,c_38470])).

tff(c_38809,plain,(
    ! [A_2576,B_2577,C_2578] : k8_relat_1('#skF_8',k6_relset_1(A_2576,B_2577,C_2578,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_2576,B_2577))))) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38496,c_38783])).

tff(c_36792,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36789,c_144])).

tff(c_40385,plain,(
    ! [B_2694,D_2695,C_2696,A_2697] :
      ( r2_hidden(B_2694,D_2695)
      | v1_xboole_0(k2_zfmisc_1(C_2696,D_2695))
      | ~ m1_subset_1(k4_tarski(A_2697,B_2694),k2_zfmisc_1(C_2696,D_2695)) ) ),
    inference(resolution,[status(thm)],[c_42,c_177])).

tff(c_40396,plain,(
    ! [B_2694,A_2697] :
      ( r2_hidden(B_2694,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(A_2697,B_2694),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36791,c_40385])).

tff(c_40404,plain,(
    ! [A_2698,B_2699] : ~ r2_hidden(k4_tarski(A_2698,B_2699),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_36792,c_38340,c_40396])).

tff(c_40418,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_2'(A_4,B_5,'#skF_9'),A_4)
      | k8_relat_1(A_4,B_5) = '#skF_9'
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_40404])).

tff(c_40461,plain,(
    ! [A_2704,B_2705] :
      ( r2_hidden('#skF_2'(A_2704,B_2705,'#skF_9'),A_2704)
      | k8_relat_1(A_2704,B_2705) = '#skF_9'
      | ~ v1_relat_1(B_2705) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_40418])).

tff(c_40506,plain,(
    ! [B_2706] :
      ( k8_relat_1('#skF_8',B_2706) = '#skF_9'
      | ~ v1_relat_1(B_2706) ) ),
    inference(resolution,[status(thm)],[c_40461,c_38340])).

tff(c_40521,plain,(
    ! [A_2576,B_2577,C_2578] : k8_relat_1('#skF_8',k6_relset_1(A_2576,B_2577,C_2578,'#skF_5'(k1_zfmisc_1(k2_zfmisc_1(A_2576,B_2577))))) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38496,c_40506])).

tff(c_40548,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38809,c_40521])).

tff(c_38843,plain,(
    ~ r2_relset_1('#skF_6','#skF_8','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38814,c_36853])).

tff(c_40569,plain,(
    ~ r2_relset_1('#skF_6','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40548,c_38843])).

tff(c_40596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38900,c_40569])).

tff(c_40599,plain,(
    ! [A_2707] : ~ r2_hidden(A_2707,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_40604,plain,(
    ! [A_44] :
      ( v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_44,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42,c_40599])).

tff(c_40648,plain,(
    ! [A_2711] : ~ m1_subset_1(A_2711,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_40604])).

tff(c_40653,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28,c_40648])).

tff(c_40654,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_40604])).

tff(c_40658,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40654,c_52])).

tff(c_40598,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_40608,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40598,c_52])).

tff(c_40622,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40608,c_60])).

tff(c_40659,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40658,c_40622])).

tff(c_40597,plain,(
    ! [A_82] : ~ r2_hidden(A_82,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_40661,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40658,c_40608])).

tff(c_40768,plain,(
    ! [A_2730,B_2731,C_2732,D_2733] :
      ( r2_hidden(k4_tarski(A_2730,B_2731),k2_zfmisc_1(C_2732,D_2733))
      | ~ r2_hidden(B_2731,D_2733)
      | ~ r2_hidden(A_2730,C_2732) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40785,plain,(
    ! [A_2730,B_2731] :
      ( r2_hidden(k4_tarski(A_2730,B_2731),'#skF_9')
      | ~ r2_hidden(B_2731,'#skF_7')
      | ~ r2_hidden(A_2730,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40661,c_40768])).

tff(c_40791,plain,(
    ! [B_2731,A_2730] :
      ( ~ r2_hidden(B_2731,'#skF_7')
      | ~ r2_hidden(A_2730,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40597,c_40785])).

tff(c_40793,plain,(
    ! [A_2734] : ~ r2_hidden(A_2734,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40791])).

tff(c_40798,plain,(
    ! [A_44] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_44,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_40793])).

tff(c_40800,plain,(
    ! [A_2735] : ~ m1_subset_1(A_2735,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40798])).

tff(c_40805,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28,c_40800])).

tff(c_40806,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_40798])).

tff(c_40664,plain,(
    ! [A_54] :
      ( A_54 = '#skF_9'
      | ~ v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40658,c_52])).

tff(c_40810,plain,(
    '#skF_6' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40806,c_40664])).

tff(c_40824,plain,(
    k2_zfmisc_1('#skF_9','#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40810,c_40661])).

tff(c_40811,plain,(
    ! [A_2736,B_2737,C_2738,D_2739] :
      ( k6_relset_1(A_2736,B_2737,C_2738,D_2739) = k8_relat_1(C_2738,D_2739)
      | ~ m1_subset_1(D_2739,k1_zfmisc_1(k2_zfmisc_1(A_2736,B_2737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40813,plain,(
    ! [C_2738,D_2739] :
      ( k6_relset_1('#skF_6','#skF_7',C_2738,D_2739) = k8_relat_1(C_2738,D_2739)
      | ~ m1_subset_1(D_2739,k1_zfmisc_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40661,c_40811])).

tff(c_40965,plain,(
    ! [C_2759,D_2760] :
      ( k6_relset_1('#skF_9','#skF_7',C_2759,D_2760) = k8_relat_1(C_2759,D_2760)
      | ~ m1_subset_1(D_2760,k1_zfmisc_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40810,c_40813])).

tff(c_41012,plain,(
    ! [C_2762] : k6_relset_1('#skF_9','#skF_7',C_2762,'#skF_9') = k8_relat_1(C_2762,'#skF_9') ),
    inference(resolution,[status(thm)],[c_40659,c_40965])).

tff(c_22,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k6_relset_1(A_22,B_23,C_24,D_25),k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41018,plain,(
    ! [C_2762] :
      ( m1_subset_1(k8_relat_1(C_2762,'#skF_9'),k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7')))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41012,c_22])).

tff(c_41026,plain,(
    ! [C_2763] : m1_subset_1(k8_relat_1(C_2763,'#skF_9'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40659,c_40824,c_40824,c_41018])).

tff(c_41058,plain,(
    ! [C_2771] : r1_tarski(k8_relat_1(C_2771,'#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_41026,c_44])).

tff(c_40758,plain,(
    ! [B_2725,A_2726,A_2727] :
      ( ~ v1_xboole_0(B_2725)
      | ~ r2_hidden(A_2726,A_2727)
      | ~ r1_tarski(A_2727,B_2725) ) ),
    inference(resolution,[status(thm)],[c_46,c_133])).

tff(c_40761,plain,(
    ! [B_2725,B_45,A_44] :
      ( ~ v1_xboole_0(B_2725)
      | ~ r1_tarski(B_45,B_2725)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_42,c_40758])).

tff(c_41060,plain,(
    ! [C_2771,A_44] :
      ( ~ v1_xboole_0('#skF_9')
      | v1_xboole_0(k8_relat_1(C_2771,'#skF_9'))
      | ~ m1_subset_1(A_44,k8_relat_1(C_2771,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_41058,c_40761])).

tff(c_41070,plain,(
    ! [C_2772,A_2773] :
      ( v1_xboole_0(k8_relat_1(C_2772,'#skF_9'))
      | ~ m1_subset_1(A_2773,k8_relat_1(C_2772,'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40654,c_41060])).

tff(c_41076,plain,(
    ! [C_2774] : v1_xboole_0(k8_relat_1(C_2774,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_28,c_41070])).

tff(c_41080,plain,(
    ! [C_2774] : k8_relat_1(C_2774,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_41076,c_40664])).

tff(c_40974,plain,(
    ! [C_2759] : k6_relset_1('#skF_9','#skF_7',C_2759,'#skF_9') = k8_relat_1(C_2759,'#skF_9') ),
    inference(resolution,[status(thm)],[c_40659,c_40965])).

tff(c_40825,plain,(
    ~ r2_relset_1('#skF_9','#skF_7',k6_relset_1('#skF_9','#skF_7','#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40810,c_40810,c_56])).

tff(c_41011,plain,(
    ~ r2_relset_1('#skF_9','#skF_7',k8_relat_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40974,c_40825])).

tff(c_41082,plain,(
    ~ r2_relset_1('#skF_9','#skF_7','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41080,c_41011])).

tff(c_40752,plain,(
    ! [C_2723,A_2724] :
      ( ~ v1_xboole_0(C_2723)
      | ~ r2_hidden(A_2724,'#skF_5'(k1_zfmisc_1(C_2723))) ) ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_40880,plain,(
    ! [C_2750,A_2751] :
      ( ~ v1_xboole_0(C_2750)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_2750)))
      | ~ m1_subset_1(A_2751,'#skF_5'(k1_zfmisc_1(C_2750))) ) ),
    inference(resolution,[status(thm)],[c_42,c_40752])).

tff(c_40907,plain,(
    ! [C_2756] :
      ( ~ v1_xboole_0(C_2756)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_2756))) ) ),
    inference(resolution,[status(thm)],[c_28,c_40880])).

tff(c_40912,plain,(
    ! [C_2757] :
      ( '#skF_5'(k1_zfmisc_1(C_2757)) = '#skF_9'
      | ~ v1_xboole_0(C_2757) ) ),
    inference(resolution,[status(thm)],[c_40907,c_40664])).

tff(c_40936,plain,(
    ! [C_2757] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(C_2757))
      | ~ v1_xboole_0(C_2757) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40912,c_28])).

tff(c_41121,plain,(
    ! [A_2777,B_2778,C_2779,D_2780] :
      ( r2_relset_1(A_2777,B_2778,C_2779,C_2779)
      | ~ m1_subset_1(D_2780,k1_zfmisc_1(k2_zfmisc_1(A_2777,B_2778)))
      | ~ m1_subset_1(C_2779,k1_zfmisc_1(k2_zfmisc_1(A_2777,B_2778))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41140,plain,(
    ! [A_2781,B_2782,C_2783] :
      ( r2_relset_1(A_2781,B_2782,C_2783,C_2783)
      | ~ m1_subset_1(C_2783,k1_zfmisc_1(k2_zfmisc_1(A_2781,B_2782))) ) ),
    inference(resolution,[status(thm)],[c_28,c_41121])).

tff(c_41158,plain,(
    ! [A_2784,B_2785] :
      ( r2_relset_1(A_2784,B_2785,'#skF_9','#skF_9')
      | ~ v1_xboole_0(k2_zfmisc_1(A_2784,B_2785)) ) ),
    inference(resolution,[status(thm)],[c_40936,c_41140])).

tff(c_41161,plain,
    ( r2_relset_1('#skF_9','#skF_7','#skF_9','#skF_9')
    | ~ v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_40824,c_41158])).

tff(c_41163,plain,(
    r2_relset_1('#skF_9','#skF_7','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40654,c_41161])).

tff(c_41165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41082,c_41163])).

tff(c_41167,plain,(
    ! [B_2786] : ~ r2_hidden(B_2786,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_40791])).

tff(c_41172,plain,(
    ! [A_44] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_44,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_41167])).

tff(c_41174,plain,(
    ! [A_2787] : ~ m1_subset_1(A_2787,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_41172])).

tff(c_41179,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28,c_41174])).

tff(c_41180,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_41172])).

tff(c_41184,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_41180,c_40664])).

tff(c_41187,plain,(
    k2_zfmisc_1('#skF_6','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41184,c_40661])).

tff(c_30,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k6_relset_1(A_30,B_31,C_32,D_33) = k8_relat_1(C_32,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_41235,plain,(
    ! [C_2795,D_2796] :
      ( k6_relset_1('#skF_6','#skF_9',C_2795,D_2796) = k8_relat_1(C_2795,D_2796)
      | ~ m1_subset_1(D_2796,k1_zfmisc_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41187,c_30])).

tff(c_41244,plain,(
    ! [C_2795] : k6_relset_1('#skF_6','#skF_9',C_2795,'#skF_9') = k8_relat_1(C_2795,'#skF_9') ),
    inference(resolution,[status(thm)],[c_40659,c_41235])).

tff(c_41456,plain,(
    ! [A_2823,B_2824,C_2825,D_2826] :
      ( m1_subset_1(k6_relset_1(A_2823,B_2824,C_2825,D_2826),k1_zfmisc_1(k2_zfmisc_1(A_2823,B_2824)))
      | ~ m1_subset_1(D_2826,k1_zfmisc_1(k2_zfmisc_1(A_2823,B_2824))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41471,plain,(
    ! [C_2795] :
      ( m1_subset_1(k8_relat_1(C_2795,'#skF_9'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_9')))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_9'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41244,c_41456])).

tff(c_41483,plain,(
    ! [C_2827] : m1_subset_1(k8_relat_1(C_2827,'#skF_9'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40659,c_41187,c_41187,c_41471])).

tff(c_41492,plain,(
    ! [A_51,C_2827] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(A_51,k8_relat_1(C_2827,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_41483,c_50])).

tff(c_41504,plain,(
    ! [A_2829,C_2830] : ~ r2_hidden(A_2829,k8_relat_1(C_2830,'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40654,c_41492])).

tff(c_41527,plain,(
    ! [C_2832,A_2833] :
      ( v1_xboole_0(k8_relat_1(C_2832,'#skF_9'))
      | ~ m1_subset_1(A_2833,k8_relat_1(C_2832,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_42,c_41504])).

tff(c_41538,plain,(
    ! [C_2834] : v1_xboole_0(k8_relat_1(C_2834,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_28,c_41527])).

tff(c_41542,plain,(
    ! [C_2834] : k8_relat_1(C_2834,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_41538,c_40664])).

tff(c_41188,plain,(
    ~ r2_relset_1('#skF_6','#skF_9',k6_relset_1('#skF_6','#skF_9','#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41184,c_41184,c_56])).

tff(c_41247,plain,(
    ~ r2_relset_1('#skF_6','#skF_9',k8_relat_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41244,c_41188])).

tff(c_41548,plain,(
    ~ r2_relset_1('#skF_6','#skF_9','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41542,c_41247])).

tff(c_41292,plain,(
    ! [C_2812,A_2813] :
      ( ~ v1_xboole_0(C_2812)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_2812)))
      | ~ m1_subset_1(A_2813,'#skF_5'(k1_zfmisc_1(C_2812))) ) ),
    inference(resolution,[status(thm)],[c_42,c_40752])).

tff(c_41297,plain,(
    ! [C_2814] :
      ( ~ v1_xboole_0(C_2814)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_2814))) ) ),
    inference(resolution,[status(thm)],[c_28,c_41292])).

tff(c_41302,plain,(
    ! [C_2815] :
      ( '#skF_5'(k1_zfmisc_1(C_2815)) = '#skF_9'
      | ~ v1_xboole_0(C_2815) ) ),
    inference(resolution,[status(thm)],[c_41297,c_40664])).

tff(c_41326,plain,(
    ! [C_2815] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(C_2815))
      | ~ v1_xboole_0(C_2815) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41302,c_28])).

tff(c_41571,plain,(
    ! [A_2836,B_2837,C_2838,D_2839] :
      ( r2_relset_1(A_2836,B_2837,C_2838,C_2838)
      | ~ m1_subset_1(D_2839,k1_zfmisc_1(k2_zfmisc_1(A_2836,B_2837)))
      | ~ m1_subset_1(C_2838,k1_zfmisc_1(k2_zfmisc_1(A_2836,B_2837))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41673,plain,(
    ! [A_2841,B_2842,C_2843] :
      ( r2_relset_1(A_2841,B_2842,C_2843,C_2843)
      | ~ m1_subset_1(C_2843,k1_zfmisc_1(k2_zfmisc_1(A_2841,B_2842))) ) ),
    inference(resolution,[status(thm)],[c_28,c_41571])).

tff(c_41706,plain,(
    ! [A_2848,B_2849] :
      ( r2_relset_1(A_2848,B_2849,'#skF_9','#skF_9')
      | ~ v1_xboole_0(k2_zfmisc_1(A_2848,B_2849)) ) ),
    inference(resolution,[status(thm)],[c_41326,c_41673])).

tff(c_41709,plain,
    ( r2_relset_1('#skF_6','#skF_9','#skF_9','#skF_9')
    | ~ v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_41187,c_41706])).

tff(c_41711,plain,(
    r2_relset_1('#skF_6','#skF_9','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40654,c_41709])).

tff(c_41713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41548,c_41711])).

%------------------------------------------------------------------------------
