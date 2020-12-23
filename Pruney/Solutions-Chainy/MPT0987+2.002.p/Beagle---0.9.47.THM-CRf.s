%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:54 EST 2020

% Result     : Theorem 8.98s
% Output     : CNFRefutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 326 expanded)
%              Number of leaves         :   37 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          :  157 (1161 expanded)
%              Number of equality atoms :   27 (  76 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,B)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & v1_funct_2(E,B,C)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
                   => ( ( v2_funct_2(D,B)
                        & v2_funct_2(E,C) )
                     => v2_funct_2(k1_partfun1(A,B,B,C,D,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_492,plain,(
    ! [C_108,A_109,E_105,F_107,D_110,B_106] :
      ( k1_partfun1(A_109,B_106,C_108,D_110,E_105,F_107) = k5_relat_1(E_105,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_108,D_110)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_109,B_106)))
      | ~ v1_funct_1(E_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_494,plain,(
    ! [A_109,B_106,E_105] :
      ( k1_partfun1(A_109,B_106,'#skF_2','#skF_3',E_105,'#skF_5') = k5_relat_1(E_105,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_109,B_106)))
      | ~ v1_funct_1(E_105) ) ),
    inference(resolution,[status(thm)],[c_40,c_492])).

tff(c_526,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_2','#skF_3',E_118,'#skF_5') = k5_relat_1(E_118,'#skF_5')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_494])).

tff(c_536,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_526])).

tff(c_543,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_536])).

tff(c_34,plain,(
    ~ v2_funct_2(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_550,plain,(
    ~ v2_funct_2(k5_relat_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_34])).

tff(c_67,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_36,plain,(
    v2_funct_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_83,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_94,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_83])).

tff(c_194,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(B_77) = A_78
      | ~ v2_funct_2(B_77,A_78)
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_203,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v2_funct_2('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_194])).

tff(c_212,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_36,c_203])).

tff(c_98,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_109,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_122,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ v4_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_131,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_122])).

tff(c_140,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_131])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_153,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_12])).

tff(c_157,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_153])).

tff(c_223,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_157])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_67])).

tff(c_38,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_96,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_200,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_194])).

tff(c_209,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_38,c_200])).

tff(c_242,plain,(
    ! [B_81,A_82] :
      ( k9_relat_1(B_81,k2_relat_1(A_82)) = k2_relat_1(k5_relat_1(A_82,B_81))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_258,plain,(
    ! [B_81] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_81)) = k9_relat_1(B_81,'#skF_2')
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_242])).

tff(c_273,plain,(
    ! [B_81] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_81)) = k9_relat_1(B_81,'#skF_2')
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_258])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_95,plain,(
    ! [A_60,B_59] : v5_relat_1(k2_zfmisc_1(A_60,B_59),B_59) ),
    inference(resolution,[status(thm)],[c_55,c_83])).

tff(c_555,plain,(
    ! [A_121,D_119,B_120,E_124,C_123,F_122] :
      ( m1_subset_1(k1_partfun1(A_121,B_120,C_123,D_119,E_124,F_122),k1_zfmisc_1(k2_zfmisc_1(A_121,D_119)))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_123,D_119)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_582,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_555])).

tff(c_598,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_40,c_582])).

tff(c_18,plain,(
    ! [C_20,A_18,B_19] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_645,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_598,c_18])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [C_6,A_3,B_4] :
      ( v5_relat_1(C_6,A_3)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(B_4))
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_615,plain,(
    ! [A_3] :
      ( v5_relat_1(k5_relat_1('#skF_4','#skF_5'),A_3)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),A_3)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_598,c_6])).

tff(c_1206,plain,(
    ! [A_151] :
      ( v5_relat_1(k5_relat_1('#skF_4','#skF_5'),A_151)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_615])).

tff(c_24,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1213,plain,
    ( v2_funct_2(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),k2_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1206,c_24])).

tff(c_1219,plain,
    ( v2_funct_2(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),k2_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_1213])).

tff(c_7619,plain,(
    ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),k2_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1219])).

tff(c_7622,plain,
    ( ~ v5_relat_1(k2_zfmisc_1('#skF_1','#skF_3'),k9_relat_1('#skF_5','#skF_2'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_7619])).

tff(c_7625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_95,c_223,c_7622])).

tff(c_7626,plain,(
    v2_funct_2(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_7630,plain,
    ( v2_funct_2(k5_relat_1('#skF_4','#skF_5'),k9_relat_1('#skF_5','#skF_2'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_7626])).

tff(c_7632,plain,(
    v2_funct_2(k5_relat_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_223,c_7630])).

tff(c_7634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_7632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.98/3.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/3.50  
% 8.98/3.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/3.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.98/3.50  
% 8.98/3.50  %Foreground sorts:
% 8.98/3.50  
% 8.98/3.50  
% 8.98/3.50  %Background operators:
% 8.98/3.50  
% 8.98/3.50  
% 8.98/3.50  %Foreground operators:
% 8.98/3.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.98/3.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.98/3.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.98/3.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.98/3.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.98/3.50  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.98/3.50  tff('#skF_5', type, '#skF_5': $i).
% 8.98/3.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.98/3.50  tff('#skF_2', type, '#skF_2': $i).
% 8.98/3.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.98/3.50  tff('#skF_3', type, '#skF_3': $i).
% 8.98/3.50  tff('#skF_1', type, '#skF_1': $i).
% 8.98/3.50  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.98/3.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.98/3.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.98/3.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.98/3.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.98/3.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.98/3.50  tff('#skF_4', type, '#skF_4': $i).
% 8.98/3.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.98/3.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.98/3.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.98/3.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.98/3.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.98/3.50  
% 8.98/3.51  tff(f_131, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_2(D, B) & v2_funct_2(E, C)) => v2_funct_2(k1_partfun1(A, B, B, C, D, E), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_funct_2)).
% 8.98/3.51  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.98/3.51  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.98/3.51  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.98/3.51  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.98/3.51  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.98/3.51  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.98/3.51  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 8.98/3.51  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.98/3.51  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.98/3.51  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.98/3.51  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.98/3.51  tff(f_38, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 8.98/3.51  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.98/3.51  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.98/3.51  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.98/3.51  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.98/3.51  tff(c_492, plain, (![C_108, A_109, E_105, F_107, D_110, B_106]: (k1_partfun1(A_109, B_106, C_108, D_110, E_105, F_107)=k5_relat_1(E_105, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_108, D_110))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_109, B_106))) | ~v1_funct_1(E_105))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.98/3.51  tff(c_494, plain, (![A_109, B_106, E_105]: (k1_partfun1(A_109, B_106, '#skF_2', '#skF_3', E_105, '#skF_5')=k5_relat_1(E_105, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_109, B_106))) | ~v1_funct_1(E_105))), inference(resolution, [status(thm)], [c_40, c_492])).
% 8.98/3.51  tff(c_526, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_2', '#skF_3', E_118, '#skF_5')=k5_relat_1(E_118, '#skF_5') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_494])).
% 8.98/3.51  tff(c_536, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_526])).
% 8.98/3.51  tff(c_543, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_536])).
% 8.98/3.51  tff(c_34, plain, (~v2_funct_2(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.98/3.51  tff(c_550, plain, (~v2_funct_2(k5_relat_1('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_543, c_34])).
% 8.98/3.51  tff(c_67, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.98/3.51  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_67])).
% 8.98/3.51  tff(c_36, plain, (v2_funct_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.98/3.51  tff(c_83, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.98/3.51  tff(c_94, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_83])).
% 8.98/3.51  tff(c_194, plain, (![B_77, A_78]: (k2_relat_1(B_77)=A_78 | ~v2_funct_2(B_77, A_78) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.98/3.51  tff(c_203, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v2_funct_2('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_94, c_194])).
% 8.98/3.51  tff(c_212, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_36, c_203])).
% 8.98/3.51  tff(c_98, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.98/3.51  tff(c_109, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_98])).
% 8.98/3.51  tff(c_122, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~v4_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.98/3.51  tff(c_131, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_109, c_122])).
% 8.98/3.51  tff(c_140, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_131])).
% 8.98/3.51  tff(c_12, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.98/3.51  tff(c_153, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_140, c_12])).
% 8.98/3.51  tff(c_157, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_153])).
% 8.98/3.51  tff(c_223, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_157])).
% 8.98/3.51  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_67])).
% 8.98/3.51  tff(c_38, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.98/3.51  tff(c_96, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_83])).
% 8.98/3.51  tff(c_200, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_194])).
% 8.98/3.51  tff(c_209, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_38, c_200])).
% 8.98/3.51  tff(c_242, plain, (![B_81, A_82]: (k9_relat_1(B_81, k2_relat_1(A_82))=k2_relat_1(k5_relat_1(A_82, B_81)) | ~v1_relat_1(B_81) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.98/3.51  tff(c_258, plain, (![B_81]: (k2_relat_1(k5_relat_1('#skF_4', B_81))=k9_relat_1(B_81, '#skF_2') | ~v1_relat_1(B_81) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_242])).
% 8.98/3.51  tff(c_273, plain, (![B_81]: (k2_relat_1(k5_relat_1('#skF_4', B_81))=k9_relat_1(B_81, '#skF_2') | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_258])).
% 8.98/3.51  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.98/3.51  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.98/3.51  tff(c_55, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 8.98/3.51  tff(c_95, plain, (![A_60, B_59]: (v5_relat_1(k2_zfmisc_1(A_60, B_59), B_59))), inference(resolution, [status(thm)], [c_55, c_83])).
% 8.98/3.51  tff(c_555, plain, (![A_121, D_119, B_120, E_124, C_123, F_122]: (m1_subset_1(k1_partfun1(A_121, B_120, C_123, D_119, E_124, F_122), k1_zfmisc_1(k2_zfmisc_1(A_121, D_119))) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_123, D_119))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.98/3.51  tff(c_582, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_543, c_555])).
% 8.98/3.51  tff(c_598, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_40, c_582])).
% 8.98/3.51  tff(c_18, plain, (![C_20, A_18, B_19]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.98/3.51  tff(c_645, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_598, c_18])).
% 8.98/3.51  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.98/3.51  tff(c_6, plain, (![C_6, A_3, B_4]: (v5_relat_1(C_6, A_3) | ~m1_subset_1(C_6, k1_zfmisc_1(B_4)) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.98/3.51  tff(c_615, plain, (![A_3]: (v5_relat_1(k5_relat_1('#skF_4', '#skF_5'), A_3) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), A_3) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_598, c_6])).
% 8.98/3.51  tff(c_1206, plain, (![A_151]: (v5_relat_1(k5_relat_1('#skF_4', '#skF_5'), A_151) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), A_151))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_615])).
% 8.98/3.51  tff(c_24, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.98/3.51  tff(c_1213, plain, (v2_funct_2(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), k2_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_1206, c_24])).
% 8.98/3.51  tff(c_1219, plain, (v2_funct_2(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), k2_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_645, c_1213])).
% 8.98/3.51  tff(c_7619, plain, (~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), k2_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1219])).
% 8.98/3.51  tff(c_7622, plain, (~v5_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'), k9_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_273, c_7619])).
% 8.98/3.51  tff(c_7625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_95, c_223, c_7622])).
% 8.98/3.51  tff(c_7626, plain, (v2_funct_2(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1219])).
% 8.98/3.51  tff(c_7630, plain, (v2_funct_2(k5_relat_1('#skF_4', '#skF_5'), k9_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_273, c_7626])).
% 8.98/3.51  tff(c_7632, plain, (v2_funct_2(k5_relat_1('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_223, c_7630])).
% 8.98/3.51  tff(c_7634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_550, c_7632])).
% 8.98/3.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.98/3.51  
% 8.98/3.51  Inference rules
% 8.98/3.51  ----------------------
% 8.98/3.51  #Ref     : 0
% 8.98/3.51  #Sup     : 1533
% 8.98/3.51  #Fact    : 0
% 8.98/3.51  #Define  : 0
% 8.98/3.51  #Split   : 12
% 8.98/3.51  #Chain   : 0
% 8.98/3.51  #Close   : 0
% 8.98/3.51  
% 8.98/3.51  Ordering : KBO
% 8.98/3.51  
% 8.98/3.51  Simplification rules
% 8.98/3.51  ----------------------
% 8.98/3.51  #Subsume      : 27
% 8.98/3.51  #Demod        : 3382
% 8.98/3.51  #Tautology    : 239
% 8.98/3.51  #SimpNegUnit  : 1
% 8.98/3.52  #BackRed      : 38
% 8.98/3.52  
% 8.98/3.52  #Partial instantiations: 0
% 8.98/3.52  #Strategies tried      : 1
% 8.98/3.52  
% 8.98/3.52  Timing (in seconds)
% 8.98/3.52  ----------------------
% 8.98/3.52  Preprocessing        : 0.35
% 8.98/3.52  Parsing              : 0.18
% 8.98/3.52  CNF conversion       : 0.03
% 8.98/3.52  Main loop            : 2.39
% 8.98/3.52  Inferencing          : 0.66
% 8.98/3.52  Reduction            : 1.10
% 8.98/3.52  Demodulation         : 0.90
% 8.98/3.52  BG Simplification    : 0.06
% 8.98/3.52  Subsumption          : 0.46
% 8.98/3.52  Abstraction          : 0.08
% 8.98/3.52  MUC search           : 0.00
% 8.98/3.52  Cooper               : 0.00
% 8.98/3.52  Total                : 2.78
% 8.98/3.52  Index Insertion      : 0.00
% 8.98/3.52  Index Deletion       : 0.00
% 8.98/3.52  Index Matching       : 0.00
% 8.98/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
