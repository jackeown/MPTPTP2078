%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:56 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 106 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 220 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_60,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_60])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(B_7,k1_tarski('#skF_1'(A_6,B_7))) = k1_xboole_0
      | r1_tarski(A_6,k2_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_tarski(A_6,k2_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    ! [B_43,A_44] :
      ( k10_relat_1(B_43,k1_tarski(A_44)) != k1_xboole_0
      | ~ r2_hidden(A_44,k2_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_319,plain,(
    ! [B_102,B_103] :
      ( k10_relat_1(B_102,k1_tarski('#skF_1'(k2_relat_1(B_102),B_103))) != k1_xboole_0
      | ~ v1_relat_1(B_102)
      | r1_tarski(k2_relat_1(B_102),k2_relat_1(B_103))
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_14,c_78])).

tff(c_324,plain,(
    ! [B_7] :
      ( r1_tarski(k2_relat_1(B_7),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_319])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_165,plain,(
    ! [B_68,A_69] :
      ( m1_subset_1(B_68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_68),A_69)))
      | ~ r1_tarski(k2_relat_1(B_68),A_69)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,B_3)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,k2_zfmisc_1(k1_relat_1(B_68),A_69))
      | ~ r1_tarski(k2_relat_1(B_68),A_69)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_165,c_4])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( k7_relset_1(A_19,B_20,C_21,D_22) = k9_relat_1(C_21,D_22)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_338,plain,(
    ! [B_106,A_107,D_108] :
      ( k7_relset_1(k1_relat_1(B_106),A_107,B_106,D_108) = k9_relat_1(B_106,D_108)
      | ~ r1_tarski(k2_relat_1(B_106),A_107)
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_165,c_22])).

tff(c_368,plain,(
    ! [B_112,D_113] :
      ( k7_relset_1(k1_relat_1(B_112),k2_relat_1(B_112),B_112,D_113) = k9_relat_1(B_112,D_113)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_324,c_338])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( m1_subset_1(k7_relset_1(A_64,B_65,C_66,D_67),k1_zfmisc_1(B_65))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_187,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( r1_tarski(k7_relset_1(A_72,B_73,C_74,D_75),B_73)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(resolution,[status(thm)],[c_141,c_4])).

tff(c_202,plain,(
    ! [A_72,B_73,A_2,D_75] :
      ( r1_tarski(k7_relset_1(A_72,B_73,A_2,D_75),B_73)
      | ~ r1_tarski(A_2,k2_zfmisc_1(A_72,B_73)) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_386,plain,(
    ! [B_114,D_115] :
      ( r1_tarski(k9_relat_1(B_114,D_115),k2_relat_1(B_114))
      | ~ r1_tarski(B_114,k2_zfmisc_1(k1_relat_1(B_114),k2_relat_1(B_114)))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_202])).

tff(c_402,plain,(
    ! [B_118,D_119] :
      ( r1_tarski(k9_relat_1(B_118,D_119),k2_relat_1(B_118))
      | ~ r1_tarski(k2_relat_1(B_118),k2_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_180,c_386])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_88,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_88])).

tff(c_203,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(k1_tarski(A_76),B_77,C_78) = k1_tarski(k1_funct_1(C_78,A_76))
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_76),B_77)))
      | ~ v1_funct_2(C_78,k1_tarski(A_76),B_77)
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_210,plain,
    ( k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5') = k1_tarski(k1_funct_1('#skF_5','#skF_2'))
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_218,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_2')) = k2_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_96,c_210])).

tff(c_219,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_2')) = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_218])).

tff(c_118,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k7_relset_1(A_55,B_56,C_57,D_58) = k9_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_124,plain,(
    ! [D_58] : k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5',D_58) = k9_relat_1('#skF_5',D_58) ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_32,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_126,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_32])).

tff(c_221,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_126])).

tff(c_405,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_402,c_221])).

tff(c_408,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_40,c_405])).

tff(c_411,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_324,c_408])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.35  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.46/1.35  
% 2.46/1.35  %Foreground sorts:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Background operators:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Foreground operators:
% 2.46/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.46/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.46/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.46/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.35  
% 2.69/1.37  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.69/1.37  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.37  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 2.69/1.37  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.69/1.37  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.69/1.37  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.69/1.37  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.69/1.37  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.69/1.37  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.69/1.37  tff(f_87, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.69/1.37  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.69/1.37  tff(c_60, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.37  tff(c_68, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_60])).
% 2.69/1.37  tff(c_12, plain, (![B_7, A_6]: (k10_relat_1(B_7, k1_tarski('#skF_1'(A_6, B_7)))=k1_xboole_0 | r1_tarski(A_6, k2_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.69/1.37  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), A_6) | r1_tarski(A_6, k2_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.69/1.37  tff(c_78, plain, (![B_43, A_44]: (k10_relat_1(B_43, k1_tarski(A_44))!=k1_xboole_0 | ~r2_hidden(A_44, k2_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.37  tff(c_319, plain, (![B_102, B_103]: (k10_relat_1(B_102, k1_tarski('#skF_1'(k2_relat_1(B_102), B_103)))!=k1_xboole_0 | ~v1_relat_1(B_102) | r1_tarski(k2_relat_1(B_102), k2_relat_1(B_103)) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_14, c_78])).
% 2.69/1.37  tff(c_324, plain, (![B_7]: (r1_tarski(k2_relat_1(B_7), k2_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_319])).
% 2.69/1.37  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.69/1.37  tff(c_165, plain, (![B_68, A_69]: (m1_subset_1(B_68, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_68), A_69))) | ~r1_tarski(k2_relat_1(B_68), A_69) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.37  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | ~m1_subset_1(A_2, k1_zfmisc_1(B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.37  tff(c_180, plain, (![B_68, A_69]: (r1_tarski(B_68, k2_zfmisc_1(k1_relat_1(B_68), A_69)) | ~r1_tarski(k2_relat_1(B_68), A_69) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_165, c_4])).
% 2.69/1.37  tff(c_22, plain, (![A_19, B_20, C_21, D_22]: (k7_relset_1(A_19, B_20, C_21, D_22)=k9_relat_1(C_21, D_22) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.37  tff(c_338, plain, (![B_106, A_107, D_108]: (k7_relset_1(k1_relat_1(B_106), A_107, B_106, D_108)=k9_relat_1(B_106, D_108) | ~r1_tarski(k2_relat_1(B_106), A_107) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_165, c_22])).
% 2.69/1.37  tff(c_368, plain, (![B_112, D_113]: (k7_relset_1(k1_relat_1(B_112), k2_relat_1(B_112), B_112, D_113)=k9_relat_1(B_112, D_113) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_324, c_338])).
% 2.69/1.37  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.37  tff(c_141, plain, (![A_64, B_65, C_66, D_67]: (m1_subset_1(k7_relset_1(A_64, B_65, C_66, D_67), k1_zfmisc_1(B_65)) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.37  tff(c_187, plain, (![A_72, B_73, C_74, D_75]: (r1_tarski(k7_relset_1(A_72, B_73, C_74, D_75), B_73) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(resolution, [status(thm)], [c_141, c_4])).
% 2.69/1.37  tff(c_202, plain, (![A_72, B_73, A_2, D_75]: (r1_tarski(k7_relset_1(A_72, B_73, A_2, D_75), B_73) | ~r1_tarski(A_2, k2_zfmisc_1(A_72, B_73)))), inference(resolution, [status(thm)], [c_6, c_187])).
% 2.69/1.37  tff(c_386, plain, (![B_114, D_115]: (r1_tarski(k9_relat_1(B_114, D_115), k2_relat_1(B_114)) | ~r1_tarski(B_114, k2_zfmisc_1(k1_relat_1(B_114), k2_relat_1(B_114))) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(superposition, [status(thm), theory('equality')], [c_368, c_202])).
% 2.69/1.37  tff(c_402, plain, (![B_118, D_119]: (r1_tarski(k9_relat_1(B_118, D_119), k2_relat_1(B_118)) | ~r1_tarski(k2_relat_1(B_118), k2_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_180, c_386])).
% 2.69/1.37  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.69/1.37  tff(c_38, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.69/1.37  tff(c_88, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.69/1.37  tff(c_96, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_88])).
% 2.69/1.37  tff(c_203, plain, (![A_76, B_77, C_78]: (k2_relset_1(k1_tarski(A_76), B_77, C_78)=k1_tarski(k1_funct_1(C_78, A_76)) | k1_xboole_0=B_77 | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_76), B_77))) | ~v1_funct_2(C_78, k1_tarski(A_76), B_77) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.69/1.37  tff(c_210, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5')=k1_tarski(k1_funct_1('#skF_5', '#skF_2')) | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_5', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_203])).
% 2.69/1.37  tff(c_218, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_2'))=k2_relat_1('#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_96, c_210])).
% 2.69/1.37  tff(c_219, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_2'))=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_218])).
% 2.69/1.37  tff(c_118, plain, (![A_55, B_56, C_57, D_58]: (k7_relset_1(A_55, B_56, C_57, D_58)=k9_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.37  tff(c_124, plain, (![D_58]: (k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', D_58)=k9_relat_1('#skF_5', D_58))), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.69/1.37  tff(c_32, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.69/1.37  tff(c_126, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_32])).
% 2.69/1.37  tff(c_221, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_126])).
% 2.69/1.37  tff(c_405, plain, (~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_402, c_221])).
% 2.69/1.37  tff(c_408, plain, (~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_40, c_405])).
% 2.69/1.37  tff(c_411, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_324, c_408])).
% 2.69/1.37  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_411])).
% 2.69/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.37  
% 2.69/1.37  Inference rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Ref     : 0
% 2.69/1.37  #Sup     : 80
% 2.69/1.37  #Fact    : 0
% 2.69/1.37  #Define  : 0
% 2.69/1.37  #Split   : 0
% 2.69/1.37  #Chain   : 0
% 2.69/1.37  #Close   : 0
% 2.69/1.37  
% 2.69/1.37  Ordering : KBO
% 2.69/1.37  
% 2.69/1.37  Simplification rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Subsume      : 3
% 2.69/1.37  #Demod        : 24
% 2.69/1.37  #Tautology    : 25
% 2.69/1.37  #SimpNegUnit  : 2
% 2.69/1.37  #BackRed      : 2
% 2.69/1.37  
% 2.69/1.37  #Partial instantiations: 0
% 2.69/1.37  #Strategies tried      : 1
% 2.69/1.37  
% 2.69/1.37  Timing (in seconds)
% 2.69/1.37  ----------------------
% 2.69/1.37  Preprocessing        : 0.31
% 2.69/1.37  Parsing              : 0.17
% 2.69/1.37  CNF conversion       : 0.02
% 2.69/1.37  Main loop            : 0.27
% 2.69/1.37  Inferencing          : 0.11
% 2.69/1.37  Reduction            : 0.08
% 2.69/1.37  Demodulation         : 0.05
% 2.69/1.37  BG Simplification    : 0.02
% 2.69/1.37  Subsumption          : 0.04
% 2.69/1.37  Abstraction          : 0.02
% 2.69/1.37  MUC search           : 0.00
% 2.69/1.37  Cooper               : 0.00
% 2.69/1.37  Total                : 0.62
% 2.69/1.37  Index Insertion      : 0.00
% 2.69/1.37  Index Deletion       : 0.00
% 2.69/1.38  Index Matching       : 0.00
% 2.69/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
