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
% DateTime   : Thu Dec  3 10:07:42 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 172 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 290 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_85,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_22,B_23)),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k8_relat_1(A_24,B_25),B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_134,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_145,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,k2_zfmisc_1('#skF_6','#skF_4'))
      | ~ r1_tarski(A_70,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_134])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_282,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_321,plain,(
    ! [A_114,B_115,A_116] :
      ( k1_relset_1(A_114,B_115,A_116) = k1_relat_1(A_116)
      | ~ r1_tarski(A_116,k2_zfmisc_1(A_114,B_115)) ) ),
    inference(resolution,[status(thm)],[c_28,c_282])).

tff(c_353,plain,(
    ! [A_117] :
      ( k1_relset_1('#skF_6','#skF_4',A_117) = k1_relat_1(A_117)
      | ~ r1_tarski(A_117,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_145,c_321])).

tff(c_369,plain,(
    ! [A_24] :
      ( k1_relset_1('#skF_6','#skF_4',k8_relat_1(A_24,'#skF_7')) = k1_relat_1(k8_relat_1(A_24,'#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_353])).

tff(c_376,plain,(
    ! [A_24] : k1_relset_1('#skF_6','#skF_4',k8_relat_1(A_24,'#skF_7')) = k1_relat_1(k8_relat_1(A_24,'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_369])).

tff(c_79,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_9,B_58] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_9),B_58),A_9)
      | r1_tarski(k1_zfmisc_1(A_9),B_58) ) ),
    inference(resolution,[status(thm)],[c_79,c_10])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_1'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_92,A_93] :
      ( r1_tarski(A_92,k1_zfmisc_1(A_93))
      | ~ r1_tarski('#skF_1'(A_92,k1_zfmisc_1(A_93)),A_93) ) ),
    inference(resolution,[status(thm)],[c_12,c_111])).

tff(c_1637,plain,(
    ! [A_235] :
      ( r1_tarski(A_235,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4')))
      | ~ r1_tarski('#skF_1'(A_235,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_145,c_222])).

tff(c_1647,plain,(
    r1_tarski(k1_zfmisc_1('#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_84,c_1637])).

tff(c_186,plain,(
    ! [A_80,C_81,B_82] :
      ( m1_subset_1(A_80,C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_194,plain,(
    ! [A_84,B_85,A_86] :
      ( m1_subset_1(A_84,B_85)
      | ~ r2_hidden(A_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(resolution,[status(thm)],[c_28,c_186])).

tff(c_203,plain,(
    ! [C_13,B_85,A_9] :
      ( m1_subset_1(C_13,B_85)
      | ~ r1_tarski(k1_zfmisc_1(A_9),B_85)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_194])).

tff(c_1676,plain,(
    ! [C_236] :
      ( m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4')))
      | ~ r1_tarski(C_236,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1647,c_203])).

tff(c_839,plain,(
    ! [A_174,B_175,C_176] :
      ( m1_subset_1(k1_relset_1(A_174,B_175,C_176),k1_zfmisc_1(A_174))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_870,plain,(
    ! [A_174,B_175,C_176] :
      ( r1_tarski(k1_relset_1(A_174,B_175,C_176),A_174)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(resolution,[status(thm)],[c_839,c_26])).

tff(c_1732,plain,(
    ! [C_238] :
      ( r1_tarski(k1_relset_1('#skF_6','#skF_4',C_238),'#skF_6')
      | ~ r1_tarski(C_238,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1676,c_870])).

tff(c_2405,plain,(
    ! [A_282] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_282,'#skF_7')),'#skF_6')
      | ~ r1_tarski(k8_relat_1(A_282,'#skF_7'),'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_1732])).

tff(c_147,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,k2_zfmisc_1('#skF_6','#skF_4'))
      | ~ r1_tarski(A_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_134])).

tff(c_93,plain,(
    ! [A_17,A_60,B_61] :
      ( v1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_155,plain,(
    ! [A_74] :
      ( v1_relat_1(A_74)
      | ~ r1_tarski(A_74,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_147,c_93])).

tff(c_167,plain,(
    ! [A_24] :
      ( v1_relat_1(k8_relat_1(A_24,'#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_173,plain,(
    ! [A_24] : v1_relat_1(k8_relat_1(A_24,'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_167])).

tff(c_998,plain,(
    ! [C_184,A_185,B_186] :
      ( m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ r1_tarski(k2_relat_1(C_184),B_186)
      | ~ r1_tarski(k1_relat_1(C_184),A_185)
      | ~ v1_relat_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_873,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k6_relset_1(A_177,B_178,C_179,D_180) = k8_relat_1(C_179,D_180)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_888,plain,(
    ! [C_179] : k6_relset_1('#skF_6','#skF_4',C_179,'#skF_7') = k8_relat_1(C_179,'#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_873])).

tff(c_46,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_6','#skF_4','#skF_5','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_946,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_5','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_46])).

tff(c_1001,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_5','#skF_7')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_5','#skF_7')),'#skF_6')
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_998,c_946])).

tff(c_1023,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_5','#skF_7')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_5','#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_1001])).

tff(c_1055,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_5','#skF_7')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1023])).

tff(c_2421,plain,(
    ~ r1_tarski(k8_relat_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2405,c_1055])).

tff(c_2503,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_2421])).

tff(c_2507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2503])).

tff(c_2508,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_5','#skF_7')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1023])).

tff(c_2512,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_2508])).

tff(c_2516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/2.03  
% 4.75/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/2.03  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 4.75/2.03  
% 4.75/2.03  %Foreground sorts:
% 4.75/2.03  
% 4.75/2.03  
% 4.75/2.03  %Background operators:
% 4.75/2.03  
% 4.75/2.03  
% 4.75/2.03  %Foreground operators:
% 4.75/2.03  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.75/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.75/2.03  tff('#skF_7', type, '#skF_7': $i).
% 4.75/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.75/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.75/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.75/2.03  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 4.75/2.03  tff('#skF_5', type, '#skF_5': $i).
% 4.75/2.03  tff('#skF_6', type, '#skF_6': $i).
% 4.75/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.75/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.75/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.75/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.75/2.03  tff('#skF_4', type, '#skF_4': $i).
% 4.75/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.75/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.75/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.75/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.75/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.75/2.03  
% 4.99/2.05  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 4.99/2.05  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.99/2.05  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 4.99/2.05  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 4.99/2.05  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.99/2.05  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.99/2.05  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.99/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.99/2.05  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.99/2.05  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.99/2.05  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.99/2.05  tff(f_96, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.99/2.05  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 4.99/2.05  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.99/2.05  tff(c_85, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.99/2.05  tff(c_94, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_48, c_85])).
% 4.99/2.05  tff(c_32, plain, (![A_22, B_23]: (r1_tarski(k2_relat_1(k8_relat_1(A_22, B_23)), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.99/2.05  tff(c_34, plain, (![A_24, B_25]: (r1_tarski(k8_relat_1(A_24, B_25), B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.99/2.05  tff(c_58, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.99/2.05  tff(c_66, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_58])).
% 4.99/2.05  tff(c_134, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.99/2.05  tff(c_145, plain, (![A_70]: (r1_tarski(A_70, k2_zfmisc_1('#skF_6', '#skF_4')) | ~r1_tarski(A_70, '#skF_7'))), inference(resolution, [status(thm)], [c_66, c_134])).
% 4.99/2.05  tff(c_28, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.99/2.05  tff(c_282, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.99/2.05  tff(c_321, plain, (![A_114, B_115, A_116]: (k1_relset_1(A_114, B_115, A_116)=k1_relat_1(A_116) | ~r1_tarski(A_116, k2_zfmisc_1(A_114, B_115)))), inference(resolution, [status(thm)], [c_28, c_282])).
% 4.99/2.05  tff(c_353, plain, (![A_117]: (k1_relset_1('#skF_6', '#skF_4', A_117)=k1_relat_1(A_117) | ~r1_tarski(A_117, '#skF_7'))), inference(resolution, [status(thm)], [c_145, c_321])).
% 4.99/2.05  tff(c_369, plain, (![A_24]: (k1_relset_1('#skF_6', '#skF_4', k8_relat_1(A_24, '#skF_7'))=k1_relat_1(k8_relat_1(A_24, '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_353])).
% 4.99/2.05  tff(c_376, plain, (![A_24]: (k1_relset_1('#skF_6', '#skF_4', k8_relat_1(A_24, '#skF_7'))=k1_relat_1(k8_relat_1(A_24, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_369])).
% 4.99/2.05  tff(c_79, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), A_57) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/2.05  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.99/2.05  tff(c_84, plain, (![A_9, B_58]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_9), B_58), A_9) | r1_tarski(k1_zfmisc_1(A_9), B_58))), inference(resolution, [status(thm)], [c_79, c_10])).
% 4.99/2.05  tff(c_12, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.99/2.05  tff(c_111, plain, (![A_65, B_66]: (~r2_hidden('#skF_1'(A_65, B_66), B_66) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/2.05  tff(c_222, plain, (![A_92, A_93]: (r1_tarski(A_92, k1_zfmisc_1(A_93)) | ~r1_tarski('#skF_1'(A_92, k1_zfmisc_1(A_93)), A_93))), inference(resolution, [status(thm)], [c_12, c_111])).
% 4.99/2.05  tff(c_1637, plain, (![A_235]: (r1_tarski(A_235, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4'))) | ~r1_tarski('#skF_1'(A_235, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4'))), '#skF_7'))), inference(resolution, [status(thm)], [c_145, c_222])).
% 4.99/2.05  tff(c_1647, plain, (r1_tarski(k1_zfmisc_1('#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(resolution, [status(thm)], [c_84, c_1637])).
% 4.99/2.05  tff(c_186, plain, (![A_80, C_81, B_82]: (m1_subset_1(A_80, C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.99/2.05  tff(c_194, plain, (![A_84, B_85, A_86]: (m1_subset_1(A_84, B_85) | ~r2_hidden(A_84, A_86) | ~r1_tarski(A_86, B_85))), inference(resolution, [status(thm)], [c_28, c_186])).
% 4.99/2.05  tff(c_203, plain, (![C_13, B_85, A_9]: (m1_subset_1(C_13, B_85) | ~r1_tarski(k1_zfmisc_1(A_9), B_85) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_12, c_194])).
% 4.99/2.05  tff(c_1676, plain, (![C_236]: (m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4'))) | ~r1_tarski(C_236, '#skF_7'))), inference(resolution, [status(thm)], [c_1647, c_203])).
% 4.99/2.05  tff(c_839, plain, (![A_174, B_175, C_176]: (m1_subset_1(k1_relset_1(A_174, B_175, C_176), k1_zfmisc_1(A_174)) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.99/2.05  tff(c_26, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.99/2.05  tff(c_870, plain, (![A_174, B_175, C_176]: (r1_tarski(k1_relset_1(A_174, B_175, C_176), A_174) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(resolution, [status(thm)], [c_839, c_26])).
% 4.99/2.05  tff(c_1732, plain, (![C_238]: (r1_tarski(k1_relset_1('#skF_6', '#skF_4', C_238), '#skF_6') | ~r1_tarski(C_238, '#skF_7'))), inference(resolution, [status(thm)], [c_1676, c_870])).
% 4.99/2.05  tff(c_2405, plain, (![A_282]: (r1_tarski(k1_relat_1(k8_relat_1(A_282, '#skF_7')), '#skF_6') | ~r1_tarski(k8_relat_1(A_282, '#skF_7'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_376, c_1732])).
% 4.99/2.05  tff(c_147, plain, (![A_73]: (r1_tarski(A_73, k2_zfmisc_1('#skF_6', '#skF_4')) | ~r1_tarski(A_73, '#skF_7'))), inference(resolution, [status(thm)], [c_66, c_134])).
% 4.99/2.05  tff(c_93, plain, (![A_17, A_60, B_61]: (v1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_60, B_61)))), inference(resolution, [status(thm)], [c_28, c_85])).
% 4.99/2.05  tff(c_155, plain, (![A_74]: (v1_relat_1(A_74) | ~r1_tarski(A_74, '#skF_7'))), inference(resolution, [status(thm)], [c_147, c_93])).
% 4.99/2.05  tff(c_167, plain, (![A_24]: (v1_relat_1(k8_relat_1(A_24, '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_155])).
% 4.99/2.05  tff(c_173, plain, (![A_24]: (v1_relat_1(k8_relat_1(A_24, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_167])).
% 4.99/2.05  tff(c_998, plain, (![C_184, A_185, B_186]: (m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~r1_tarski(k2_relat_1(C_184), B_186) | ~r1_tarski(k1_relat_1(C_184), A_185) | ~v1_relat_1(C_184))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.99/2.05  tff(c_873, plain, (![A_177, B_178, C_179, D_180]: (k6_relset_1(A_177, B_178, C_179, D_180)=k8_relat_1(C_179, D_180) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.99/2.05  tff(c_888, plain, (![C_179]: (k6_relset_1('#skF_6', '#skF_4', C_179, '#skF_7')=k8_relat_1(C_179, '#skF_7'))), inference(resolution, [status(thm)], [c_48, c_873])).
% 4.99/2.05  tff(c_46, plain, (~m1_subset_1(k6_relset_1('#skF_6', '#skF_4', '#skF_5', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.99/2.05  tff(c_946, plain, (~m1_subset_1(k8_relat_1('#skF_5', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_46])).
% 4.99/2.05  tff(c_1001, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_5', '#skF_7')), '#skF_5') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_5', '#skF_7')), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_998, c_946])).
% 4.99/2.05  tff(c_1023, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_5', '#skF_7')), '#skF_5') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_5', '#skF_7')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_1001])).
% 4.99/2.05  tff(c_1055, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_5', '#skF_7')), '#skF_6')), inference(splitLeft, [status(thm)], [c_1023])).
% 4.99/2.05  tff(c_2421, plain, (~r1_tarski(k8_relat_1('#skF_5', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_2405, c_1055])).
% 4.99/2.05  tff(c_2503, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_34, c_2421])).
% 4.99/2.05  tff(c_2507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_2503])).
% 4.99/2.05  tff(c_2508, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_5', '#skF_7')), '#skF_5')), inference(splitRight, [status(thm)], [c_1023])).
% 4.99/2.05  tff(c_2512, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_2508])).
% 4.99/2.05  tff(c_2516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_2512])).
% 4.99/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/2.05  
% 4.99/2.05  Inference rules
% 4.99/2.05  ----------------------
% 4.99/2.05  #Ref     : 0
% 4.99/2.05  #Sup     : 572
% 4.99/2.05  #Fact    : 0
% 4.99/2.05  #Define  : 0
% 4.99/2.05  #Split   : 8
% 4.99/2.05  #Chain   : 0
% 4.99/2.05  #Close   : 0
% 4.99/2.05  
% 4.99/2.05  Ordering : KBO
% 4.99/2.05  
% 4.99/2.05  Simplification rules
% 4.99/2.05  ----------------------
% 4.99/2.05  #Subsume      : 83
% 4.99/2.05  #Demod        : 61
% 4.99/2.05  #Tautology    : 44
% 4.99/2.05  #SimpNegUnit  : 25
% 4.99/2.05  #BackRed      : 2
% 4.99/2.05  
% 4.99/2.05  #Partial instantiations: 0
% 4.99/2.05  #Strategies tried      : 1
% 4.99/2.05  
% 4.99/2.05  Timing (in seconds)
% 4.99/2.05  ----------------------
% 4.99/2.05  Preprocessing        : 0.35
% 4.99/2.05  Parsing              : 0.18
% 4.99/2.05  CNF conversion       : 0.03
% 4.99/2.05  Main loop            : 0.79
% 4.99/2.05  Inferencing          : 0.26
% 4.99/2.05  Reduction            : 0.25
% 4.99/2.05  Demodulation         : 0.17
% 4.99/2.05  BG Simplification    : 0.04
% 4.99/2.05  Subsumption          : 0.18
% 4.99/2.05  Abstraction          : 0.04
% 4.99/2.05  MUC search           : 0.00
% 4.99/2.05  Cooper               : 0.00
% 4.99/2.05  Total                : 1.18
% 4.99/2.05  Index Insertion      : 0.00
% 4.99/2.05  Index Deletion       : 0.00
% 4.99/2.05  Index Matching       : 0.00
% 4.99/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
