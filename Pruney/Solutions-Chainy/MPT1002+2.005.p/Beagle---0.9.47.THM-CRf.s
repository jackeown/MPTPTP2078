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
% DateTime   : Thu Dec  3 10:13:57 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 188 expanded)
%              Number of leaves         :   34 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 442 expanded)
%              Number of equality atoms :   31 ( 134 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_48,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_143,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_153,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_149])).

tff(c_209,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_224,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_209])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_409,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k8_relset_1(A_95,B_96,C_97,D_98) = k10_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_420,plain,(
    ! [D_98] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_98) = k10_relat_1('#skF_4',D_98) ),
    inference(resolution,[status(thm)],[c_50,c_409])).

tff(c_613,plain,(
    ! [B_124,A_125,C_126] :
      ( k1_xboole_0 = B_124
      | k8_relset_1(A_125,B_124,C_126,B_124) = A_125
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_2(C_126,A_125,B_124)
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_620,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_613])).

tff(c_626,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_4','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_420,c_620])).

tff(c_627,plain,(
    k10_relat_1('#skF_4','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_626])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k10_relat_1(B_16,A_15),k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_635,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_28])).

tff(c_642,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_635])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_657,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_642,c_2])).

tff(c_658,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_661,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_658])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_224,c_661])).

tff(c_666,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,k10_relat_1(B_18,k9_relat_1(B_18,A_17)))
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_333,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k7_relset_1(A_87,B_88,C_89,D_90) = k9_relat_1(C_89,D_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_344,plain,(
    ! [D_90] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_90) = k9_relat_1('#skF_4',D_90) ),
    inference(resolution,[status(thm)],[c_50,c_333])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_354,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_44])).

tff(c_490,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_354])).

tff(c_493,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_490])).

tff(c_496,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_493])).

tff(c_670,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_496])).

tff(c_674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_670])).

tff(c_675,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_677,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_8])).

tff(c_781,plain,(
    ! [B_144,A_145] :
      ( B_144 = A_145
      | ~ r1_tarski(B_144,A_145)
      | ~ r1_tarski(A_145,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_791,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_781])).

tff(c_803,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_791])).

tff(c_676,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_682,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_676])).

tff(c_763,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_682,c_44])).

tff(c_804,plain,(
    ~ r1_tarski('#skF_1',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_803,c_763])).

tff(c_809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.43  
% 2.71/1.43  %Foreground sorts:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Background operators:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Foreground operators:
% 2.71/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.71/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.71/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.71/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.71/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.43  
% 2.71/1.45  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 2.71/1.45  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.71/1.45  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.45  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.71/1.45  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.71/1.45  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.71/1.45  tff(f_94, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.71/1.45  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.71/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.45  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.71/1.45  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.71/1.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.71/1.45  tff(c_48, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.71/1.45  tff(c_26, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.45  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.71/1.45  tff(c_143, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.45  tff(c_149, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_143])).
% 2.71/1.45  tff(c_153, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_149])).
% 2.71/1.45  tff(c_209, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.71/1.45  tff(c_224, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_209])).
% 2.71/1.45  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.71/1.45  tff(c_46, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.71/1.45  tff(c_59, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_46])).
% 2.71/1.45  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.71/1.45  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.71/1.45  tff(c_409, plain, (![A_95, B_96, C_97, D_98]: (k8_relset_1(A_95, B_96, C_97, D_98)=k10_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.45  tff(c_420, plain, (![D_98]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_98)=k10_relat_1('#skF_4', D_98))), inference(resolution, [status(thm)], [c_50, c_409])).
% 2.71/1.45  tff(c_613, plain, (![B_124, A_125, C_126]: (k1_xboole_0=B_124 | k8_relset_1(A_125, B_124, C_126, B_124)=A_125 | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_2(C_126, A_125, B_124) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.71/1.45  tff(c_620, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_613])).
% 2.71/1.45  tff(c_626, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_4', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_420, c_620])).
% 2.71/1.45  tff(c_627, plain, (k10_relat_1('#skF_4', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_59, c_626])).
% 2.71/1.45  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k10_relat_1(B_16, A_15), k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.71/1.45  tff(c_635, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_627, c_28])).
% 2.71/1.45  tff(c_642, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_635])).
% 2.71/1.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.45  tff(c_657, plain, (k1_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_642, c_2])).
% 2.71/1.45  tff(c_658, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_657])).
% 2.71/1.45  tff(c_661, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_658])).
% 2.71/1.45  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_224, c_661])).
% 2.71/1.45  tff(c_666, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_657])).
% 2.71/1.45  tff(c_30, plain, (![A_17, B_18]: (r1_tarski(A_17, k10_relat_1(B_18, k9_relat_1(B_18, A_17))) | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.71/1.45  tff(c_333, plain, (![A_87, B_88, C_89, D_90]: (k7_relset_1(A_87, B_88, C_89, D_90)=k9_relat_1(C_89, D_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.45  tff(c_344, plain, (![D_90]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_90)=k9_relat_1('#skF_4', D_90))), inference(resolution, [status(thm)], [c_50, c_333])).
% 2.71/1.45  tff(c_44, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.71/1.45  tff(c_354, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_44])).
% 2.71/1.45  tff(c_490, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_354])).
% 2.71/1.45  tff(c_493, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_490])).
% 2.71/1.45  tff(c_496, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_493])).
% 2.71/1.45  tff(c_670, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_666, c_496])).
% 2.71/1.45  tff(c_674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_670])).
% 2.71/1.45  tff(c_675, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 2.71/1.45  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.45  tff(c_677, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_8])).
% 2.71/1.45  tff(c_781, plain, (![B_144, A_145]: (B_144=A_145 | ~r1_tarski(B_144, A_145) | ~r1_tarski(A_145, B_144))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.45  tff(c_791, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_781])).
% 2.71/1.45  tff(c_803, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_677, c_791])).
% 2.71/1.45  tff(c_676, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 2.71/1.45  tff(c_682, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_675, c_676])).
% 2.71/1.45  tff(c_763, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_682, c_682, c_44])).
% 2.71/1.45  tff(c_804, plain, (~r1_tarski('#skF_1', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_803, c_803, c_763])).
% 2.71/1.45  tff(c_809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_677, c_804])).
% 2.71/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.45  
% 2.71/1.45  Inference rules
% 2.71/1.45  ----------------------
% 2.71/1.45  #Ref     : 0
% 2.71/1.45  #Sup     : 156
% 2.71/1.45  #Fact    : 0
% 2.71/1.45  #Define  : 0
% 2.71/1.45  #Split   : 6
% 2.71/1.45  #Chain   : 0
% 2.71/1.45  #Close   : 0
% 2.71/1.45  
% 2.71/1.45  Ordering : KBO
% 2.71/1.45  
% 2.71/1.45  Simplification rules
% 2.71/1.45  ----------------------
% 2.71/1.45  #Subsume      : 25
% 2.71/1.45  #Demod        : 121
% 2.71/1.45  #Tautology    : 77
% 2.71/1.45  #SimpNegUnit  : 12
% 2.71/1.45  #BackRed      : 14
% 2.71/1.45  
% 2.71/1.45  #Partial instantiations: 0
% 2.71/1.45  #Strategies tried      : 1
% 2.71/1.45  
% 2.71/1.45  Timing (in seconds)
% 2.71/1.45  ----------------------
% 2.71/1.45  Preprocessing        : 0.33
% 2.71/1.45  Parsing              : 0.18
% 2.71/1.45  CNF conversion       : 0.02
% 2.71/1.45  Main loop            : 0.34
% 2.71/1.45  Inferencing          : 0.12
% 2.71/1.45  Reduction            : 0.11
% 2.71/1.45  Demodulation         : 0.08
% 2.71/1.45  BG Simplification    : 0.02
% 2.71/1.45  Subsumption          : 0.06
% 2.71/1.45  Abstraction          : 0.02
% 2.71/1.45  MUC search           : 0.00
% 2.71/1.45  Cooper               : 0.00
% 2.71/1.45  Total                : 0.71
% 2.71/1.45  Index Insertion      : 0.00
% 2.71/1.45  Index Deletion       : 0.00
% 2.71/1.45  Index Matching       : 0.00
% 2.71/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
