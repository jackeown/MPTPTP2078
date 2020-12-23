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
% DateTime   : Thu Dec  3 10:13:57 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 181 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 456 expanded)
%              Number of equality atoms :   40 ( 186 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_35,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_41,plain,(
    ! [A_23,B_24,C_25] :
      ( k1_relset_1(A_23,B_24,C_25) = k1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_96,plain,(
    ! [B_48,A_49,C_50] :
      ( k1_xboole_0 = B_48
      | k1_relset_1(A_49,B_48,C_50) = A_49
      | ~ v1_funct_2(C_50,A_49,B_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_96])).

tff(c_102,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_45,c_99])).

tff(c_103,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_102])).

tff(c_36,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,k10_relat_1(B_2,k9_relat_1(B_2,A_1)))
      | ~ r1_tarski(A_1,k1_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( k8_relset_1(A_36,B_37,C_38,D_39) = k10_relat_1(C_38,D_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [D_39] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_39) = k10_relat_1('#skF_4',D_39) ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_52,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k7_relset_1(A_29,B_30,C_31,D_32) = k9_relat_1(C_31,D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [D_32] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_32) = k9_relat_1('#skF_4',D_32) ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_24])).

tff(c_71,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56])).

tff(c_83,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_86,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83])).

tff(c_104,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_86])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_110,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_115,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_110])).

tff(c_116,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_32])).

tff(c_121,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_30])).

tff(c_128,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_128])).

tff(c_20,plain,(
    ! [B_18,C_19] :
      ( k1_relset_1(k1_xboole_0,B_18,C_19) = k1_xboole_0
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_184,plain,(
    ! [B_72,C_73] :
      ( k1_relset_1('#skF_1',B_72,C_73) = '#skF_1'
      | ~ v1_funct_2(C_73,'#skF_1',B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_72))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_109,c_109,c_109,c_20])).

tff(c_187,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_121,c_184])).

tff(c_190,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_132,c_187])).

tff(c_122,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_122])).

tff(c_154,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k8_relset_1(A_65,B_66,C_67,D_68) = k10_relat_1(C_67,D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [D_68] : k8_relset_1('#skF_1','#skF_1','#skF_4',D_68) = k10_relat_1('#skF_4',D_68) ),
    inference(resolution,[status(thm)],[c_121,c_154])).

tff(c_140,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k7_relset_1(A_60,B_61,C_62,D_63) = k9_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_143,plain,(
    ! [D_63] : k7_relset_1('#skF_1','#skF_1','#skF_4',D_63) = k9_relat_1('#skF_4',D_63) ),
    inference(resolution,[status(thm)],[c_121,c_140])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_24])).

tff(c_144,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_127])).

tff(c_158,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_144])).

tff(c_170,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_158])).

tff(c_173,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_170])).

tff(c_191,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_173])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.25  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.14/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.14/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.25  
% 2.14/1.27  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 2.14/1.27  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.14/1.27  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.14/1.27  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.27  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.14/1.27  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.14/1.27  tff(f_43, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.14/1.27  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.14/1.27  tff(c_26, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.14/1.27  tff(c_35, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.14/1.27  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.14/1.27  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.14/1.27  tff(c_41, plain, (![A_23, B_24, C_25]: (k1_relset_1(A_23, B_24, C_25)=k1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.27  tff(c_45, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.14/1.27  tff(c_96, plain, (![B_48, A_49, C_50]: (k1_xboole_0=B_48 | k1_relset_1(A_49, B_48, C_50)=A_49 | ~v1_funct_2(C_50, A_49, B_48) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.27  tff(c_99, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_96])).
% 2.14/1.27  tff(c_102, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_45, c_99])).
% 2.14/1.27  tff(c_103, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_35, c_102])).
% 2.14/1.27  tff(c_36, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.27  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_36])).
% 2.14/1.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k10_relat_1(B_2, k9_relat_1(B_2, A_1))) | ~r1_tarski(A_1, k1_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.27  tff(c_67, plain, (![A_36, B_37, C_38, D_39]: (k8_relset_1(A_36, B_37, C_38, D_39)=k10_relat_1(C_38, D_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.27  tff(c_70, plain, (![D_39]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_39)=k10_relat_1('#skF_4', D_39))), inference(resolution, [status(thm)], [c_30, c_67])).
% 2.14/1.27  tff(c_52, plain, (![A_29, B_30, C_31, D_32]: (k7_relset_1(A_29, B_30, C_31, D_32)=k9_relat_1(C_31, D_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.27  tff(c_55, plain, (![D_32]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_32)=k9_relat_1('#skF_4', D_32))), inference(resolution, [status(thm)], [c_30, c_52])).
% 2.14/1.27  tff(c_24, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.14/1.27  tff(c_56, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_24])).
% 2.14/1.27  tff(c_71, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56])).
% 2.14/1.27  tff(c_83, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.14/1.27  tff(c_86, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83])).
% 2.14/1.27  tff(c_104, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_86])).
% 2.14/1.27  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_104])).
% 2.14/1.27  tff(c_109, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.14/1.27  tff(c_110, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.14/1.27  tff(c_115, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_110])).
% 2.14/1.27  tff(c_116, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_32])).
% 2.14/1.27  tff(c_121, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_30])).
% 2.14/1.27  tff(c_128, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.27  tff(c_132, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_121, c_128])).
% 2.14/1.27  tff(c_20, plain, (![B_18, C_19]: (k1_relset_1(k1_xboole_0, B_18, C_19)=k1_xboole_0 | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.27  tff(c_184, plain, (![B_72, C_73]: (k1_relset_1('#skF_1', B_72, C_73)='#skF_1' | ~v1_funct_2(C_73, '#skF_1', B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_72))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_109, c_109, c_109, c_20])).
% 2.14/1.27  tff(c_187, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_121, c_184])).
% 2.14/1.27  tff(c_190, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_132, c_187])).
% 2.14/1.27  tff(c_122, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.27  tff(c_126, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_121, c_122])).
% 2.14/1.27  tff(c_154, plain, (![A_65, B_66, C_67, D_68]: (k8_relset_1(A_65, B_66, C_67, D_68)=k10_relat_1(C_67, D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.27  tff(c_157, plain, (![D_68]: (k8_relset_1('#skF_1', '#skF_1', '#skF_4', D_68)=k10_relat_1('#skF_4', D_68))), inference(resolution, [status(thm)], [c_121, c_154])).
% 2.14/1.27  tff(c_140, plain, (![A_60, B_61, C_62, D_63]: (k7_relset_1(A_60, B_61, C_62, D_63)=k9_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.27  tff(c_143, plain, (![D_63]: (k7_relset_1('#skF_1', '#skF_1', '#skF_4', D_63)=k9_relat_1('#skF_4', D_63))), inference(resolution, [status(thm)], [c_121, c_140])).
% 2.14/1.27  tff(c_127, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_24])).
% 2.14/1.27  tff(c_144, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_127])).
% 2.14/1.27  tff(c_158, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_144])).
% 2.14/1.27  tff(c_170, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_158])).
% 2.14/1.27  tff(c_173, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_170])).
% 2.14/1.27  tff(c_191, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_173])).
% 2.14/1.27  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_191])).
% 2.14/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  Inference rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Ref     : 0
% 2.14/1.27  #Sup     : 30
% 2.14/1.27  #Fact    : 0
% 2.14/1.27  #Define  : 0
% 2.14/1.27  #Split   : 1
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 0
% 2.14/1.27  #Demod        : 37
% 2.14/1.27  #Tautology    : 18
% 2.14/1.27  #SimpNegUnit  : 2
% 2.14/1.27  #BackRed      : 9
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.27  Preprocessing        : 0.32
% 2.14/1.27  Parsing              : 0.17
% 2.14/1.27  CNF conversion       : 0.02
% 2.14/1.27  Main loop            : 0.17
% 2.14/1.27  Inferencing          : 0.06
% 2.14/1.27  Reduction            : 0.06
% 2.14/1.27  Demodulation         : 0.04
% 2.14/1.27  BG Simplification    : 0.01
% 2.14/1.27  Subsumption          : 0.02
% 2.14/1.27  Abstraction          : 0.01
% 2.14/1.27  MUC search           : 0.00
% 2.14/1.27  Cooper               : 0.00
% 2.14/1.27  Total                : 0.52
% 2.14/1.27  Index Insertion      : 0.00
% 2.14/1.27  Index Deletion       : 0.00
% 2.14/1.27  Index Matching       : 0.00
% 2.14/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
