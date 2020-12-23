%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:56 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 127 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 257 expanded)
%              Number of equality atoms :   37 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_57])).

tff(c_285,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_289,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_285])).

tff(c_44,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_61,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_290,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_61])).

tff(c_90,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_90])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_257,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(A_86,k2_relat_1(B_87))
      | k10_relat_1(B_87,k1_tarski(A_86)) = k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_323,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(A_105,k2_relat_1(B_106))
      | k10_relat_1(B_106,k1_tarski('#skF_1'(A_105,k2_relat_1(B_106)))) = k1_xboole_0
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_257,c_4])).

tff(c_308,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k8_relset_1(A_99,B_100,C_101,D_102) = k10_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_311,plain,(
    ! [D_102] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_102) = k10_relat_1('#skF_4',D_102) ),
    inference(resolution,[status(thm)],[c_34,c_308])).

tff(c_50,plain,(
    ! [D_29] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_29)) != k1_xboole_0
      | ~ r2_hidden(D_29,'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_222,plain,(
    ! [D_29] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski(D_29)) != k1_xboole_0
      | ~ r2_hidden(D_29,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_50])).

tff(c_312,plain,(
    ! [D_29] :
      ( k10_relat_1('#skF_4',k1_tarski(D_29)) != k1_xboole_0
      | ~ r2_hidden(D_29,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_222])).

tff(c_330,plain,(
    ! [A_105] :
      ( ~ r2_hidden('#skF_1'(A_105,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_105,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_312])).

tff(c_339,plain,(
    ! [A_107] :
      ( ~ r2_hidden('#skF_1'(A_107,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_107,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_330])).

tff(c_349,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_339])).

tff(c_86,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(B_47) = A_48
      | ~ r1_tarski(A_48,k2_relat_1(B_47))
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_354,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_349,c_89])).

tff(c_367,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94,c_354])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_367])).

tff(c_371,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_480,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_483,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_480])).

tff(c_485,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_483])).

tff(c_370,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_422,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r2_hidden(C_125,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_428,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_5',B_126)
      | ~ r1_tarski('#skF_3',B_126) ) ),
    inference(resolution,[status(thm)],[c_370,c_422])).

tff(c_449,plain,(
    ! [B_133,A_134] :
      ( k10_relat_1(B_133,k1_tarski(A_134)) != k1_xboole_0
      | ~ r2_hidden(A_134,k2_relat_1(B_133))
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_462,plain,(
    ! [B_133] :
      ( k10_relat_1(B_133,k1_tarski('#skF_5')) != k1_xboole_0
      | ~ v1_relat_1(B_133)
      | ~ r1_tarski('#skF_3',k2_relat_1(B_133)) ) ),
    inference(resolution,[status(thm)],[c_428,c_449])).

tff(c_489,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_462])).

tff(c_508,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_60,c_489])).

tff(c_533,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k8_relset_1(A_143,B_144,C_145,D_146) = k10_relat_1(C_145,D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_542,plain,(
    ! [D_148] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_148) = k10_relat_1('#skF_4',D_148) ),
    inference(resolution,[status(thm)],[c_34,c_533])).

tff(c_40,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_404,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_40])).

tff(c_548,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_404])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.42  
% 2.49/1.42  %Foreground sorts:
% 2.49/1.42  
% 2.49/1.42  
% 2.49/1.42  %Background operators:
% 2.49/1.42  
% 2.49/1.42  
% 2.49/1.42  %Foreground operators:
% 2.49/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.49/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.49/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.49/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.42  
% 2.49/1.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.49/1.44  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.49/1.44  tff(f_89, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_2)).
% 2.49/1.44  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.49/1.44  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.49/1.44  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.49/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.49/1.44  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.49/1.44  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.49/1.44  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.49/1.44  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.49/1.44  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.44  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.49/1.44  tff(c_54, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.49/1.44  tff(c_57, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.49/1.44  tff(c_60, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_57])).
% 2.49/1.44  tff(c_285, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.49/1.44  tff(c_289, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_285])).
% 2.49/1.44  tff(c_44, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.49/1.44  tff(c_61, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_44])).
% 2.49/1.44  tff(c_290, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_61])).
% 2.49/1.44  tff(c_90, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.44  tff(c_94, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_90])).
% 2.49/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.44  tff(c_257, plain, (![A_86, B_87]: (r2_hidden(A_86, k2_relat_1(B_87)) | k10_relat_1(B_87, k1_tarski(A_86))=k1_xboole_0 | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.44  tff(c_323, plain, (![A_105, B_106]: (r1_tarski(A_105, k2_relat_1(B_106)) | k10_relat_1(B_106, k1_tarski('#skF_1'(A_105, k2_relat_1(B_106))))=k1_xboole_0 | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_257, c_4])).
% 2.49/1.44  tff(c_308, plain, (![A_99, B_100, C_101, D_102]: (k8_relset_1(A_99, B_100, C_101, D_102)=k10_relat_1(C_101, D_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.44  tff(c_311, plain, (![D_102]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_102)=k10_relat_1('#skF_4', D_102))), inference(resolution, [status(thm)], [c_34, c_308])).
% 2.49/1.44  tff(c_50, plain, (![D_29]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_29))!=k1_xboole_0 | ~r2_hidden(D_29, '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.49/1.44  tff(c_222, plain, (![D_29]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski(D_29))!=k1_xboole_0 | ~r2_hidden(D_29, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_61, c_50])).
% 2.49/1.44  tff(c_312, plain, (![D_29]: (k10_relat_1('#skF_4', k1_tarski(D_29))!=k1_xboole_0 | ~r2_hidden(D_29, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_222])).
% 2.49/1.44  tff(c_330, plain, (![A_105]: (~r2_hidden('#skF_1'(A_105, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_105, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_323, c_312])).
% 2.49/1.44  tff(c_339, plain, (![A_107]: (~r2_hidden('#skF_1'(A_107, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_107, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_330])).
% 2.49/1.44  tff(c_349, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_339])).
% 2.49/1.44  tff(c_86, plain, (![B_47, A_48]: (r1_tarski(k2_relat_1(B_47), A_48) | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.44  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.49/1.44  tff(c_89, plain, (![B_47, A_48]: (k2_relat_1(B_47)=A_48 | ~r1_tarski(A_48, k2_relat_1(B_47)) | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_86, c_8])).
% 2.49/1.44  tff(c_354, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_349, c_89])).
% 2.49/1.44  tff(c_367, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94, c_354])).
% 2.49/1.44  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_367])).
% 2.49/1.44  tff(c_371, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.49/1.44  tff(c_480, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.49/1.44  tff(c_483, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_480])).
% 2.49/1.44  tff(c_485, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_371, c_483])).
% 2.49/1.44  tff(c_370, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.49/1.44  tff(c_422, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~r2_hidden(C_125, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.44  tff(c_428, plain, (![B_126]: (r2_hidden('#skF_5', B_126) | ~r1_tarski('#skF_3', B_126))), inference(resolution, [status(thm)], [c_370, c_422])).
% 2.49/1.44  tff(c_449, plain, (![B_133, A_134]: (k10_relat_1(B_133, k1_tarski(A_134))!=k1_xboole_0 | ~r2_hidden(A_134, k2_relat_1(B_133)) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.44  tff(c_462, plain, (![B_133]: (k10_relat_1(B_133, k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1(B_133) | ~r1_tarski('#skF_3', k2_relat_1(B_133)))), inference(resolution, [status(thm)], [c_428, c_449])).
% 2.49/1.44  tff(c_489, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_485, c_462])).
% 2.49/1.44  tff(c_508, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_60, c_489])).
% 2.49/1.44  tff(c_533, plain, (![A_143, B_144, C_145, D_146]: (k8_relset_1(A_143, B_144, C_145, D_146)=k10_relat_1(C_145, D_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.44  tff(c_542, plain, (![D_148]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_148)=k10_relat_1('#skF_4', D_148))), inference(resolution, [status(thm)], [c_34, c_533])).
% 2.49/1.44  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.49/1.44  tff(c_404, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_371, c_40])).
% 2.49/1.44  tff(c_548, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_542, c_404])).
% 2.49/1.44  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_548])).
% 2.49/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.44  
% 2.49/1.44  Inference rules
% 2.49/1.44  ----------------------
% 2.49/1.44  #Ref     : 0
% 2.49/1.44  #Sup     : 104
% 2.49/1.44  #Fact    : 0
% 2.49/1.44  #Define  : 0
% 2.49/1.44  #Split   : 2
% 2.49/1.44  #Chain   : 0
% 2.49/1.44  #Close   : 0
% 2.49/1.44  
% 2.49/1.44  Ordering : KBO
% 2.49/1.44  
% 2.49/1.44  Simplification rules
% 2.49/1.44  ----------------------
% 2.49/1.44  #Subsume      : 6
% 2.49/1.44  #Demod        : 35
% 2.49/1.44  #Tautology    : 41
% 2.49/1.44  #SimpNegUnit  : 5
% 2.49/1.44  #BackRed      : 4
% 2.49/1.44  
% 2.49/1.44  #Partial instantiations: 0
% 2.49/1.44  #Strategies tried      : 1
% 2.49/1.44  
% 2.49/1.44  Timing (in seconds)
% 2.49/1.44  ----------------------
% 2.49/1.44  Preprocessing        : 0.34
% 2.49/1.44  Parsing              : 0.18
% 2.49/1.44  CNF conversion       : 0.02
% 2.49/1.44  Main loop            : 0.29
% 2.49/1.44  Inferencing          : 0.12
% 2.49/1.44  Reduction            : 0.08
% 2.49/1.44  Demodulation         : 0.06
% 2.49/1.44  BG Simplification    : 0.02
% 2.49/1.44  Subsumption          : 0.05
% 2.49/1.44  Abstraction          : 0.02
% 2.49/1.44  MUC search           : 0.00
% 2.49/1.44  Cooper               : 0.00
% 2.49/1.44  Total                : 0.66
% 2.49/1.44  Index Insertion      : 0.00
% 2.49/1.44  Index Deletion       : 0.00
% 2.49/1.44  Index Matching       : 0.00
% 2.49/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
