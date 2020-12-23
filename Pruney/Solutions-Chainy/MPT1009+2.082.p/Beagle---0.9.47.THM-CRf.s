%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:53 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 226 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 420 expanded)
%              Number of equality atoms :   38 ( 136 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_162,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_175,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_162])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k2_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_184,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_175,c_32])).

tff(c_186,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_290,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_303,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_290])).

tff(c_318,plain,(
    ! [A_82,B_83,C_84] :
      ( m1_subset_1(k1_relset_1(A_82,B_83,C_84),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_334,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_318])).

tff(c_343,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_334])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_352,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_343,c_18])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_tarski(B_5) = A_4
      | k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_tarski(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_355,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_352,c_10])).

tff(c_360,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_355])).

tff(c_34,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(k1_funct_1(B_16,A_15)) = k2_relat_1(B_16)
      | k1_tarski(A_15) != k1_relat_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_369,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_48])).

tff(c_42,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k7_relset_1(A_26,B_27,C_28,D_29) = k9_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_430,plain,(
    ! [D_29] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_29) = k9_relat_1('#skF_4',D_29) ),
    inference(resolution,[status(thm)],[c_369,c_42])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_367,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_44])).

tff(c_486,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_367])).

tff(c_498,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_486])).

tff(c_500,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_52,c_360,c_498])).

tff(c_503,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_500])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_503])).

tff(c_508,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_514,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_83])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k9_relat_1(B_41,A_42),k2_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [A_42] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_42),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_93])).

tff(c_97,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_127,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_138,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_127])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_138])).

tff(c_145,plain,(
    ! [A_42] : r1_tarski(k9_relat_1(k1_xboole_0,A_42),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_572,plain,(
    ! [A_102] : r1_tarski(k9_relat_1('#skF_4',A_102),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_508,c_145])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_574,plain,(
    ! [A_102] :
      ( k9_relat_1('#skF_4',A_102) = '#skF_4'
      | ~ r1_tarski('#skF_4',k9_relat_1('#skF_4',A_102)) ) ),
    inference(resolution,[status(thm)],[c_572,c_2])).

tff(c_577,plain,(
    ! [A_102] : k9_relat_1('#skF_4',A_102) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_574])).

tff(c_515,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_16])).

tff(c_957,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k7_relset_1(A_158,B_159,C_160,D_161) = k9_relat_1(C_160,D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_965,plain,(
    ! [A_158,B_159,D_161] : k7_relset_1(A_158,B_159,'#skF_4',D_161) = k9_relat_1('#skF_4',D_161) ),
    inference(resolution,[status(thm)],[c_515,c_957])).

tff(c_971,plain,(
    ! [A_158,B_159,D_161] : k7_relset_1(A_158,B_159,'#skF_4',D_161) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_965])).

tff(c_973,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_44])).

tff(c_976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:38:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.48  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.07/1.48  
% 3.07/1.48  %Foreground sorts:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Background operators:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Foreground operators:
% 3.07/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.07/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.07/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.48  
% 3.21/1.50  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.21/1.50  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.21/1.50  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.21/1.50  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.21/1.50  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.21/1.50  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.21/1.50  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.50  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.21/1.50  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.21/1.50  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.21/1.50  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.21/1.50  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.21/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.50  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.50  tff(c_162, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.50  tff(c_175, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_162])).
% 3.21/1.50  tff(c_24, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, A_12), k2_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.50  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.50  tff(c_32, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.21/1.50  tff(c_184, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_175, c_32])).
% 3.21/1.50  tff(c_186, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_184])).
% 3.21/1.50  tff(c_290, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.21/1.50  tff(c_303, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_290])).
% 3.21/1.50  tff(c_318, plain, (![A_82, B_83, C_84]: (m1_subset_1(k1_relset_1(A_82, B_83, C_84), k1_zfmisc_1(A_82)) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.21/1.50  tff(c_334, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_303, c_318])).
% 3.21/1.50  tff(c_343, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_334])).
% 3.21/1.50  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.50  tff(c_352, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_343, c_18])).
% 3.21/1.50  tff(c_10, plain, (![B_5, A_4]: (k1_tarski(B_5)=A_4 | k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.50  tff(c_355, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_352, c_10])).
% 3.21/1.50  tff(c_360, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_186, c_355])).
% 3.21/1.50  tff(c_34, plain, (![B_16, A_15]: (k1_tarski(k1_funct_1(B_16, A_15))=k2_relat_1(B_16) | k1_tarski(A_15)!=k1_relat_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.21/1.50  tff(c_369, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_48])).
% 3.21/1.50  tff(c_42, plain, (![A_26, B_27, C_28, D_29]: (k7_relset_1(A_26, B_27, C_28, D_29)=k9_relat_1(C_28, D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.50  tff(c_430, plain, (![D_29]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_29)=k9_relat_1('#skF_4', D_29))), inference(resolution, [status(thm)], [c_369, c_42])).
% 3.21/1.50  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.50  tff(c_367, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_44])).
% 3.21/1.50  tff(c_486, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_367])).
% 3.21/1.50  tff(c_498, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_486])).
% 3.21/1.50  tff(c_500, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_52, c_360, c_498])).
% 3.21/1.50  tff(c_503, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_500])).
% 3.21/1.50  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_503])).
% 3.21/1.50  tff(c_508, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_184])).
% 3.21/1.50  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.50  tff(c_75, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.50  tff(c_83, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_16, c_75])).
% 3.21/1.50  tff(c_514, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_83])).
% 3.21/1.50  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.50  tff(c_93, plain, (![B_41, A_42]: (r1_tarski(k9_relat_1(B_41, A_42), k2_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.50  tff(c_96, plain, (![A_42]: (r1_tarski(k9_relat_1(k1_xboole_0, A_42), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_93])).
% 3.21/1.50  tff(c_97, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_96])).
% 3.21/1.50  tff(c_127, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.50  tff(c_138, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_127])).
% 3.21/1.50  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_138])).
% 3.21/1.50  tff(c_145, plain, (![A_42]: (r1_tarski(k9_relat_1(k1_xboole_0, A_42), k1_xboole_0))), inference(splitRight, [status(thm)], [c_96])).
% 3.21/1.50  tff(c_572, plain, (![A_102]: (r1_tarski(k9_relat_1('#skF_4', A_102), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_508, c_145])).
% 3.21/1.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.50  tff(c_574, plain, (![A_102]: (k9_relat_1('#skF_4', A_102)='#skF_4' | ~r1_tarski('#skF_4', k9_relat_1('#skF_4', A_102)))), inference(resolution, [status(thm)], [c_572, c_2])).
% 3.21/1.50  tff(c_577, plain, (![A_102]: (k9_relat_1('#skF_4', A_102)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_574])).
% 3.21/1.50  tff(c_515, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_16])).
% 3.21/1.50  tff(c_957, plain, (![A_158, B_159, C_160, D_161]: (k7_relset_1(A_158, B_159, C_160, D_161)=k9_relat_1(C_160, D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.50  tff(c_965, plain, (![A_158, B_159, D_161]: (k7_relset_1(A_158, B_159, '#skF_4', D_161)=k9_relat_1('#skF_4', D_161))), inference(resolution, [status(thm)], [c_515, c_957])).
% 3.21/1.50  tff(c_971, plain, (![A_158, B_159, D_161]: (k7_relset_1(A_158, B_159, '#skF_4', D_161)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_965])).
% 3.21/1.50  tff(c_973, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_971, c_44])).
% 3.21/1.50  tff(c_976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_973])).
% 3.21/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  Inference rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Ref     : 0
% 3.21/1.50  #Sup     : 189
% 3.21/1.50  #Fact    : 0
% 3.21/1.50  #Define  : 0
% 3.21/1.50  #Split   : 5
% 3.21/1.50  #Chain   : 0
% 3.21/1.50  #Close   : 0
% 3.21/1.50  
% 3.21/1.50  Ordering : KBO
% 3.21/1.50  
% 3.21/1.50  Simplification rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Subsume      : 4
% 3.21/1.50  #Demod        : 136
% 3.21/1.50  #Tautology    : 106
% 3.21/1.50  #SimpNegUnit  : 4
% 3.21/1.50  #BackRed      : 23
% 3.21/1.50  
% 3.21/1.50  #Partial instantiations: 0
% 3.21/1.50  #Strategies tried      : 1
% 3.21/1.50  
% 3.21/1.50  Timing (in seconds)
% 3.21/1.50  ----------------------
% 3.21/1.51  Preprocessing        : 0.34
% 3.21/1.51  Parsing              : 0.18
% 3.21/1.51  CNF conversion       : 0.02
% 3.21/1.51  Main loop            : 0.38
% 3.21/1.51  Inferencing          : 0.14
% 3.21/1.51  Reduction            : 0.12
% 3.21/1.51  Demodulation         : 0.09
% 3.21/1.51  BG Simplification    : 0.02
% 3.21/1.51  Subsumption          : 0.07
% 3.21/1.51  Abstraction          : 0.02
% 3.21/1.51  MUC search           : 0.00
% 3.21/1.51  Cooper               : 0.00
% 3.21/1.51  Total                : 0.75
% 3.21/1.51  Index Insertion      : 0.00
% 3.21/1.51  Index Deletion       : 0.00
% 3.21/1.51  Index Matching       : 0.00
% 3.21/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
