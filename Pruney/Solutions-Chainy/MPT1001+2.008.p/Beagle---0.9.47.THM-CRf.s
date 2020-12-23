%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:56 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 129 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 259 expanded)
%              Number of equality atoms :   36 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_205,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_209,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_44,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_63,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_210,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_63])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_87,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_91,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_87])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14),A_13)
      | r1_tarski(A_13,k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k10_relat_1(B_14,k1_tarski('#skF_1'(A_13,B_14))) = k1_xboole_0
      | r1_tarski(A_13,k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_236,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k8_relset_1(A_83,B_84,C_85,D_86) = k10_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_239,plain,(
    ! [D_86] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_86) = k10_relat_1('#skF_4',D_86) ),
    inference(resolution,[status(thm)],[c_34,c_236])).

tff(c_50,plain,(
    ! [D_28] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_203,plain,(
    ! [D_28] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_28)) != k1_xboole_0
      | ~ r2_hidden(D_28,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50])).

tff(c_250,plain,(
    ! [D_88] :
      ( k10_relat_1('#skF_4',k1_tarski(D_88)) != k1_xboole_0
      | ~ r2_hidden(D_88,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_203])).

tff(c_254,plain,(
    ! [A_13] :
      ( ~ r2_hidden('#skF_1'(A_13,'#skF_4'),'#skF_3')
      | r1_tarski(A_13,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_250])).

tff(c_258,plain,(
    ! [A_89] :
      ( ~ r2_hidden('#skF_1'(A_89,'#skF_4'),'#skF_3')
      | r1_tarski(A_89,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_254])).

tff(c_262,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_258])).

tff(c_265,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_262])).

tff(c_78,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k2_relat_1(B_37),A_38)
      | ~ v5_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [B_37,A_38] :
      ( k2_relat_1(B_37) = A_38
      | ~ r1_tarski(A_38,k2_relat_1(B_37))
      | ~ v5_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_269,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_265,c_81])).

tff(c_274,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_91,c_269])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_274])).

tff(c_277,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_482,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k8_relset_1(A_124,B_125,C_126,D_127) = k10_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_487,plain,(
    ! [D_128] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_128) = k10_relat_1('#skF_4',D_128) ),
    inference(resolution,[status(thm)],[c_34,c_482])).

tff(c_278,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_309,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_40])).

tff(c_493,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_309])).

tff(c_290,plain,(
    ! [B_92,A_93] :
      ( v1_relat_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_293,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_296,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_293])).

tff(c_340,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_343,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_340])).

tff(c_345,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_343])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k1_tarski(A_11)) != k1_xboole_0
      | ~ r2_hidden(A_11,k2_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_352,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_4',k1_tarski(A_11)) != k1_xboole_0
      | ~ r2_hidden(A_11,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_20])).

tff(c_367,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_4',k1_tarski(A_11)) != k1_xboole_0
      | ~ r2_hidden(A_11,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_352])).

tff(c_508,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_367])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.33  
% 2.68/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.33  
% 2.68/1.33  %Foreground sorts:
% 2.68/1.33  
% 2.68/1.33  
% 2.68/1.33  %Background operators:
% 2.68/1.33  
% 2.68/1.33  
% 2.68/1.33  %Foreground operators:
% 2.68/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.68/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.33  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.68/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.68/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.68/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.68/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.68/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.33  
% 2.68/1.35  tff(f_94, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_2)).
% 2.68/1.35  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.68/1.35  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.68/1.35  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.68/1.35  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.68/1.35  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 2.68/1.35  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.68/1.35  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.68/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.35  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.68/1.35  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.35  tff(c_205, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.35  tff(c_209, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_205])).
% 2.68/1.35  tff(c_44, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.35  tff(c_63, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_44])).
% 2.68/1.35  tff(c_210, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_63])).
% 2.68/1.35  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.35  tff(c_71, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.68/1.35  tff(c_74, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.68/1.35  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_74])).
% 2.68/1.35  tff(c_87, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.68/1.35  tff(c_91, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_87])).
% 2.68/1.35  tff(c_24, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14), A_13) | r1_tarski(A_13, k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.35  tff(c_22, plain, (![B_14, A_13]: (k10_relat_1(B_14, k1_tarski('#skF_1'(A_13, B_14)))=k1_xboole_0 | r1_tarski(A_13, k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.35  tff(c_236, plain, (![A_83, B_84, C_85, D_86]: (k8_relset_1(A_83, B_84, C_85, D_86)=k10_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.35  tff(c_239, plain, (![D_86]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_86)=k10_relat_1('#skF_4', D_86))), inference(resolution, [status(thm)], [c_34, c_236])).
% 2.68/1.35  tff(c_50, plain, (![D_28]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.35  tff(c_203, plain, (![D_28]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_28))!=k1_xboole_0 | ~r2_hidden(D_28, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_50])).
% 2.68/1.35  tff(c_250, plain, (![D_88]: (k10_relat_1('#skF_4', k1_tarski(D_88))!=k1_xboole_0 | ~r2_hidden(D_88, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_203])).
% 2.68/1.35  tff(c_254, plain, (![A_13]: (~r2_hidden('#skF_1'(A_13, '#skF_4'), '#skF_3') | r1_tarski(A_13, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_250])).
% 2.68/1.35  tff(c_258, plain, (![A_89]: (~r2_hidden('#skF_1'(A_89, '#skF_4'), '#skF_3') | r1_tarski(A_89, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_254])).
% 2.68/1.35  tff(c_262, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_258])).
% 2.68/1.35  tff(c_265, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_262])).
% 2.68/1.35  tff(c_78, plain, (![B_37, A_38]: (r1_tarski(k2_relat_1(B_37), A_38) | ~v5_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.35  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.35  tff(c_81, plain, (![B_37, A_38]: (k2_relat_1(B_37)=A_38 | ~r1_tarski(A_38, k2_relat_1(B_37)) | ~v5_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.68/1.35  tff(c_269, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_265, c_81])).
% 2.68/1.35  tff(c_274, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_91, c_269])).
% 2.68/1.35  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_274])).
% 2.68/1.35  tff(c_277, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.68/1.35  tff(c_482, plain, (![A_124, B_125, C_126, D_127]: (k8_relset_1(A_124, B_125, C_126, D_127)=k10_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.35  tff(c_487, plain, (![D_128]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_128)=k10_relat_1('#skF_4', D_128))), inference(resolution, [status(thm)], [c_34, c_482])).
% 2.68/1.35  tff(c_278, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.68/1.35  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.35  tff(c_309, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_278, c_40])).
% 2.68/1.35  tff(c_493, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_487, c_309])).
% 2.68/1.35  tff(c_290, plain, (![B_92, A_93]: (v1_relat_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.68/1.35  tff(c_293, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_290])).
% 2.68/1.35  tff(c_296, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_293])).
% 2.68/1.35  tff(c_340, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.35  tff(c_343, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_340])).
% 2.68/1.35  tff(c_345, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_343])).
% 2.68/1.35  tff(c_20, plain, (![B_12, A_11]: (k10_relat_1(B_12, k1_tarski(A_11))!=k1_xboole_0 | ~r2_hidden(A_11, k2_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.35  tff(c_352, plain, (![A_11]: (k10_relat_1('#skF_4', k1_tarski(A_11))!=k1_xboole_0 | ~r2_hidden(A_11, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_345, c_20])).
% 2.68/1.35  tff(c_367, plain, (![A_11]: (k10_relat_1('#skF_4', k1_tarski(A_11))!=k1_xboole_0 | ~r2_hidden(A_11, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_352])).
% 2.68/1.35  tff(c_508, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_493, c_367])).
% 2.68/1.35  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_508])).
% 2.68/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.35  
% 2.68/1.35  Inference rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Ref     : 0
% 2.68/1.35  #Sup     : 90
% 2.68/1.35  #Fact    : 0
% 2.68/1.35  #Define  : 0
% 2.68/1.35  #Split   : 2
% 2.68/1.35  #Chain   : 0
% 2.68/1.35  #Close   : 0
% 2.68/1.35  
% 2.68/1.35  Ordering : KBO
% 2.68/1.35  
% 2.68/1.35  Simplification rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Subsume      : 4
% 2.68/1.35  #Demod        : 53
% 2.68/1.35  #Tautology    : 52
% 2.68/1.35  #SimpNegUnit  : 4
% 2.68/1.35  #BackRed      : 4
% 2.68/1.35  
% 2.68/1.35  #Partial instantiations: 0
% 2.68/1.35  #Strategies tried      : 1
% 2.68/1.35  
% 2.68/1.35  Timing (in seconds)
% 2.68/1.35  ----------------------
% 2.68/1.35  Preprocessing        : 0.33
% 2.68/1.35  Parsing              : 0.18
% 2.68/1.35  CNF conversion       : 0.02
% 2.68/1.35  Main loop            : 0.26
% 2.68/1.35  Inferencing          : 0.10
% 2.68/1.35  Reduction            : 0.07
% 2.68/1.35  Demodulation         : 0.06
% 2.68/1.35  BG Simplification    : 0.02
% 2.68/1.35  Subsumption          : 0.04
% 2.68/1.35  Abstraction          : 0.01
% 2.68/1.35  MUC search           : 0.00
% 2.68/1.35  Cooper               : 0.00
% 2.68/1.35  Total                : 0.62
% 2.68/1.35  Index Insertion      : 0.00
% 2.68/1.35  Index Deletion       : 0.00
% 2.68/1.35  Index Matching       : 0.00
% 2.68/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
