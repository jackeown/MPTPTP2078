%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:51 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 135 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 219 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_54])).

tff(c_259,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_267,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_259])).

tff(c_382,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r2_relset_1(A_105,B_106,C_107,C_107)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_389,plain,(
    ! [C_109] :
      ( r2_relset_1('#skF_1','#skF_2',C_109,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_382])).

tff(c_392,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_389])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_336,plain,(
    ! [B_99,A_100] :
      ( k5_relat_1(B_99,k6_partfun1(A_100)) = B_99
      | ~ r1_tarski(k2_relat_1(B_99),A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_340,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_336])).

tff(c_26,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_33,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_398,plain,(
    ! [B_115,A_116,F_117,D_118,E_114,C_113] :
      ( k4_relset_1(A_116,B_115,C_113,D_118,E_114,F_117) = k5_relat_1(E_114,F_117)
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_113,D_118)))
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_414,plain,(
    ! [A_122,B_123,A_124,E_125] :
      ( k4_relset_1(A_122,B_123,A_124,A_124,E_125,k6_partfun1(A_124)) = k5_relat_1(E_125,k6_partfun1(A_124))
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(resolution,[status(thm)],[c_33,c_398])).

tff(c_420,plain,(
    ! [A_124] : k4_relset_1('#skF_1','#skF_2',A_124,A_124,'#skF_3',k6_partfun1(A_124)) = k5_relat_1('#skF_3',k6_partfun1(A_124)) ),
    inference(resolution,[status(thm)],[c_32,c_414])).

tff(c_202,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_relset_1(A_65,B_66,C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_214,plain,(
    ! [C_72] :
      ( r2_relset_1('#skF_1','#skF_2',C_72,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_202])).

tff(c_217,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_214])).

tff(c_64,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_72,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_83,plain,(
    ! [B_49,A_50] :
      ( k7_relat_1(B_49,A_50) = B_49
      | ~ v4_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_83])).

tff(c_95,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_89])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_16])).

tff(c_104,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_100])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,(
    ! [A_60,B_61] :
      ( k5_relat_1(k6_partfun1(A_60),B_61) = B_61
      | ~ r1_tarski(k1_relat_1(B_61),A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_146,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_140])).

tff(c_155,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_146])).

tff(c_218,plain,(
    ! [A_76,B_75,C_73,D_78,E_74,F_77] :
      ( k4_relset_1(A_76,B_75,C_73,D_78,E_74,F_77) = k5_relat_1(E_74,F_77)
      | ~ m1_subset_1(F_77,k1_zfmisc_1(k2_zfmisc_1(C_73,D_78)))
      | ~ m1_subset_1(E_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_225,plain,(
    ! [A_79,B_80,E_81] :
      ( k4_relset_1(A_79,B_80,'#skF_1','#skF_2',E_81,'#skF_3') = k5_relat_1(E_81,'#skF_3')
      | ~ m1_subset_1(E_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(resolution,[status(thm)],[c_32,c_218])).

tff(c_232,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_225])).

tff(c_30,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_63,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_238,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_63])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_155,c_238])).

tff(c_242,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_425,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_242])).

tff(c_437,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_425])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_267,c_392,c_437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.33  
% 2.27/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.33  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.33  
% 2.27/1.33  %Foreground sorts:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Background operators:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Foreground operators:
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.33  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.27/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.27/1.33  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.33  
% 2.58/1.35  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.58/1.35  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.58/1.35  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.58/1.35  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.35  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.58/1.35  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.58/1.35  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.58/1.35  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.58/1.35  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.58/1.35  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.58/1.35  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.58/1.35  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.58/1.35  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.58/1.35  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.35  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.58/1.35  tff(c_48, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.35  tff(c_54, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.58/1.35  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_54])).
% 2.58/1.35  tff(c_259, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.35  tff(c_267, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_259])).
% 2.58/1.35  tff(c_382, plain, (![A_105, B_106, C_107, D_108]: (r2_relset_1(A_105, B_106, C_107, C_107) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.58/1.35  tff(c_389, plain, (![C_109]: (r2_relset_1('#skF_1', '#skF_2', C_109, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_382])).
% 2.58/1.35  tff(c_392, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_389])).
% 2.58/1.35  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.35  tff(c_28, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.58/1.35  tff(c_14, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.58/1.35  tff(c_336, plain, (![B_99, A_100]: (k5_relat_1(B_99, k6_partfun1(A_100))=B_99 | ~r1_tarski(k2_relat_1(B_99), A_100) | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14])).
% 2.58/1.35  tff(c_340, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_336])).
% 2.58/1.35  tff(c_26, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.35  tff(c_33, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.58/1.35  tff(c_398, plain, (![B_115, A_116, F_117, D_118, E_114, C_113]: (k4_relset_1(A_116, B_115, C_113, D_118, E_114, F_117)=k5_relat_1(E_114, F_117) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_113, D_118))) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.58/1.35  tff(c_414, plain, (![A_122, B_123, A_124, E_125]: (k4_relset_1(A_122, B_123, A_124, A_124, E_125, k6_partfun1(A_124))=k5_relat_1(E_125, k6_partfun1(A_124)) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(resolution, [status(thm)], [c_33, c_398])).
% 2.58/1.35  tff(c_420, plain, (![A_124]: (k4_relset_1('#skF_1', '#skF_2', A_124, A_124, '#skF_3', k6_partfun1(A_124))=k5_relat_1('#skF_3', k6_partfun1(A_124)))), inference(resolution, [status(thm)], [c_32, c_414])).
% 2.58/1.35  tff(c_202, plain, (![A_65, B_66, C_67, D_68]: (r2_relset_1(A_65, B_66, C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.58/1.35  tff(c_214, plain, (![C_72]: (r2_relset_1('#skF_1', '#skF_2', C_72, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_202])).
% 2.58/1.35  tff(c_217, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_214])).
% 2.58/1.35  tff(c_64, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.35  tff(c_72, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_64])).
% 2.58/1.35  tff(c_83, plain, (![B_49, A_50]: (k7_relat_1(B_49, A_50)=B_49 | ~v4_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.35  tff(c_89, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_83])).
% 2.58/1.35  tff(c_95, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_89])).
% 2.58/1.35  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.58/1.35  tff(c_100, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_95, c_16])).
% 2.58/1.35  tff(c_104, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_100])).
% 2.58/1.35  tff(c_12, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.35  tff(c_140, plain, (![A_60, B_61]: (k5_relat_1(k6_partfun1(A_60), B_61)=B_61 | ~r1_tarski(k1_relat_1(B_61), A_60) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 2.58/1.35  tff(c_146, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_140])).
% 2.58/1.35  tff(c_155, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_146])).
% 2.58/1.35  tff(c_218, plain, (![A_76, B_75, C_73, D_78, E_74, F_77]: (k4_relset_1(A_76, B_75, C_73, D_78, E_74, F_77)=k5_relat_1(E_74, F_77) | ~m1_subset_1(F_77, k1_zfmisc_1(k2_zfmisc_1(C_73, D_78))) | ~m1_subset_1(E_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.58/1.35  tff(c_225, plain, (![A_79, B_80, E_81]: (k4_relset_1(A_79, B_80, '#skF_1', '#skF_2', E_81, '#skF_3')=k5_relat_1(E_81, '#skF_3') | ~m1_subset_1(E_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(resolution, [status(thm)], [c_32, c_218])).
% 2.58/1.35  tff(c_232, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_33, c_225])).
% 2.58/1.35  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.58/1.35  tff(c_63, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.58/1.35  tff(c_238, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_63])).
% 2.58/1.35  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_155, c_238])).
% 2.58/1.35  tff(c_242, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.58/1.35  tff(c_425, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_420, c_242])).
% 2.58/1.35  tff(c_437, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_340, c_425])).
% 2.58/1.35  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_267, c_392, c_437])).
% 2.58/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  Inference rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Ref     : 0
% 2.58/1.35  #Sup     : 87
% 2.58/1.35  #Fact    : 0
% 2.58/1.35  #Define  : 0
% 2.58/1.35  #Split   : 1
% 2.58/1.35  #Chain   : 0
% 2.58/1.35  #Close   : 0
% 2.58/1.35  
% 2.58/1.35  Ordering : KBO
% 2.58/1.35  
% 2.58/1.35  Simplification rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Subsume      : 0
% 2.58/1.35  #Demod        : 52
% 2.58/1.35  #Tautology    : 42
% 2.58/1.35  #SimpNegUnit  : 0
% 2.58/1.35  #BackRed      : 2
% 2.58/1.35  
% 2.58/1.35  #Partial instantiations: 0
% 2.58/1.35  #Strategies tried      : 1
% 2.58/1.35  
% 2.58/1.35  Timing (in seconds)
% 2.58/1.35  ----------------------
% 2.58/1.35  Preprocessing        : 0.32
% 2.58/1.35  Parsing              : 0.18
% 2.58/1.35  CNF conversion       : 0.02
% 2.58/1.35  Main loop            : 0.26
% 2.58/1.35  Inferencing          : 0.11
% 2.58/1.36  Reduction            : 0.08
% 2.58/1.36  Demodulation         : 0.06
% 2.58/1.36  BG Simplification    : 0.01
% 2.58/1.36  Subsumption          : 0.03
% 2.58/1.36  Abstraction          : 0.02
% 2.58/1.36  MUC search           : 0.00
% 2.58/1.36  Cooper               : 0.00
% 2.58/1.36  Total                : 0.62
% 2.58/1.36  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
