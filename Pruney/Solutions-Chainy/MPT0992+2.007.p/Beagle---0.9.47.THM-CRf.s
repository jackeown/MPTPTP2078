%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:32 EST 2020

% Result     : Theorem 9.65s
% Output     : CNFRefutation 9.99s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 953 expanded)
%              Number of leaves         :   36 ( 313 expanded)
%              Depth                    :   13
%              Number of atoms          :  278 (3191 expanded)
%              Number of equality atoms :   82 (1112 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_52,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_62,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_65,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_62])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14842,plain,(
    ! [A_784,B_785,C_786] :
      ( k1_relset_1(A_784,B_785,C_786) = k1_relat_1(C_786)
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_784,B_785))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14850,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_14842])).

tff(c_15058,plain,(
    ! [B_817,A_818,C_819] :
      ( k1_xboole_0 = B_817
      | k1_relset_1(A_818,B_817,C_819) = A_818
      | ~ v1_funct_2(C_819,A_818,B_817)
      | ~ m1_subset_1(C_819,k1_zfmisc_1(k2_zfmisc_1(A_818,B_817))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_15067,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_15058])).

tff(c_15073,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14850,c_15067])).

tff(c_15074,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_15073])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k7_relat_1(B_12,A_11)) = A_11
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15089,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15074,c_14])).

tff(c_15097,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_15089])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14967,plain,(
    ! [A_810,B_811,C_812,D_813] :
      ( k2_partfun1(A_810,B_811,C_812,D_813) = k7_relat_1(C_812,D_813)
      | ~ m1_subset_1(C_812,k1_zfmisc_1(k2_zfmisc_1(A_810,B_811)))
      | ~ v1_funct_1(C_812) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14973,plain,(
    ! [D_813] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_813) = k7_relat_1('#skF_4',D_813)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_14967])).

tff(c_14980,plain,(
    ! [D_813] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_813) = k7_relat_1('#skF_4',D_813) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14973])).

tff(c_262,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k2_partfun1(A_112,B_113,C_114,D_115) = k7_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_266,plain,(
    ! [D_115] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_115) = k7_relat_1('#skF_4',D_115)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_262])).

tff(c_270,plain,(
    ! [D_115] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_115) = k7_relat_1('#skF_4',D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_266])).

tff(c_550,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( m1_subset_1(k2_partfun1(A_145,B_146,C_147,D_148),k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_590,plain,(
    ! [D_115] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_115),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_550])).

tff(c_607,plain,(
    ! [D_149] : m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_590])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_650,plain,(
    ! [D_149] : v1_relat_1(k7_relat_1('#skF_4',D_149)) ),
    inference(resolution,[status(thm)],[c_607,c_16])).

tff(c_18,plain,(
    ! [C_18,B_17,A_16] :
      ( v5_relat_1(C_18,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_648,plain,(
    ! [D_149] : v5_relat_1(k7_relat_1('#skF_4',D_149),'#skF_2') ),
    inference(resolution,[status(thm)],[c_607,c_18])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_194,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( v1_funct_1(k2_partfun1(A_92,B_93,C_94,D_95))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_196,plain,(
    ! [D_95] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_95))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_194])).

tff(c_199,plain,(
    ! [D_95] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_196])).

tff(c_271,plain,(
    ! [D_95] : v1_funct_1(k7_relat_1('#skF_4',D_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_199])).

tff(c_184,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_188,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_184])).

tff(c_314,plain,(
    ! [B_122,A_123,C_124] :
      ( k1_xboole_0 = B_122
      | k1_relset_1(A_123,B_122,C_124) = A_123
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_320,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_314])).

tff(c_324,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_188,c_320])).

tff(c_325,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_324])).

tff(c_343,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_14])).

tff(c_367,plain,(
    ! [A_126] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_126)) = A_126
      | ~ r1_tarski(A_126,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_343])).

tff(c_42,plain,(
    ! [B_34,A_33] :
      ( m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_34),A_33)))
      | ~ r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_380,plain,(
    ! [A_126,A_33] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_126),k1_zfmisc_1(k2_zfmisc_1(A_126,A_33)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_126)),A_33)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_126))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_126))
      | ~ r1_tarski(A_126,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_42])).

tff(c_404,plain,(
    ! [A_126,A_33] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_126),k1_zfmisc_1(k2_zfmisc_1(A_126,A_33)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_126)),A_33)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_126))
      | ~ r1_tarski(A_126,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_380])).

tff(c_14678,plain,(
    ! [A_777,A_778] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_777),k1_zfmisc_1(k2_zfmisc_1(A_777,A_778)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_777)),A_778)
      | ~ r1_tarski(A_777,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_404])).

tff(c_126,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( v1_funct_1(k2_partfun1(A_64,B_65,C_66,D_67))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_128,plain,(
    ! [D_67] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_67))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_131,plain,(
    ! [D_67] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_128])).

tff(c_48,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_69,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_69])).

tff(c_135,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_165,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_272,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_165])).

tff(c_14706,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_14678,c_272])).

tff(c_14772,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14706])).

tff(c_14793,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_14772])).

tff(c_14797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_648,c_14793])).

tff(c_14798,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_14990,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14980,c_14798])).

tff(c_14799,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_14849,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14799,c_14842])).

tff(c_14985,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14980,c_14980,c_14849])).

tff(c_14989,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14980,c_14799])).

tff(c_15169,plain,(
    ! [B_823,C_824,A_825] :
      ( k1_xboole_0 = B_823
      | v1_funct_2(C_824,A_825,B_823)
      | k1_relset_1(A_825,B_823,C_824) != A_825
      | ~ m1_subset_1(C_824,k1_zfmisc_1(k2_zfmisc_1(A_825,B_823))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_15172,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_14989,c_15169])).

tff(c_15180,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14985,c_15172])).

tff(c_15181,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14990,c_59,c_15180])).

tff(c_15189,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15097,c_15181])).

tff(c_15193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_15189])).

tff(c_15194,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_15195,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_15200,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15194,c_15195])).

tff(c_15201,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15200,c_56])).

tff(c_15206,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15200,c_54])).

tff(c_15742,plain,(
    ! [A_917,B_918,C_919] :
      ( k1_relset_1(A_917,B_918,C_919) = k1_relat_1(C_919)
      | ~ m1_subset_1(C_919,k1_zfmisc_1(k2_zfmisc_1(A_917,B_918))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_15750,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15206,c_15742])).

tff(c_32,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_15852,plain,(
    ! [B_934,C_935] :
      ( k1_relset_1('#skF_1',B_934,C_935) = '#skF_1'
      | ~ v1_funct_2(C_935,'#skF_1',B_934)
      | ~ m1_subset_1(C_935,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_934))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15194,c_15194,c_15194,c_15194,c_32])).

tff(c_15858,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_15206,c_15852])).

tff(c_15863,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15201,c_15750,c_15858])).

tff(c_15224,plain,(
    ! [B_829,A_830] :
      ( v1_relat_1(B_829)
      | ~ m1_subset_1(B_829,k1_zfmisc_1(A_830))
      | ~ v1_relat_1(A_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15227,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_15206,c_15224])).

tff(c_15230,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_15227])).

tff(c_15237,plain,(
    ! [C_834,A_835,B_836] :
      ( v4_relat_1(C_834,A_835)
      | ~ m1_subset_1(C_834,k1_zfmisc_1(k2_zfmisc_1(A_835,B_836))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_15241,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_15206,c_15237])).

tff(c_15344,plain,(
    ! [B_864,A_865] :
      ( k7_relat_1(B_864,A_865) = B_864
      | ~ v4_relat_1(B_864,A_865)
      | ~ v1_relat_1(B_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_15347,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15241,c_15344])).

tff(c_15350,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15230,c_15347])).

tff(c_16139,plain,(
    ! [A_958,B_959,C_960,D_961] :
      ( k2_partfun1(A_958,B_959,C_960,D_961) = k7_relat_1(C_960,D_961)
      | ~ m1_subset_1(C_960,k1_zfmisc_1(k2_zfmisc_1(A_958,B_959)))
      | ~ v1_funct_1(C_960) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16147,plain,(
    ! [D_961] :
      ( k2_partfun1('#skF_1','#skF_1','#skF_4',D_961) = k7_relat_1('#skF_4',D_961)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15206,c_16139])).

tff(c_16157,plain,(
    ! [D_961] : k2_partfun1('#skF_1','#skF_1','#skF_4',D_961) = k7_relat_1('#skF_4',D_961) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16147])).

tff(c_15624,plain,(
    ! [A_905,B_906,C_907,D_908] :
      ( k2_partfun1(A_905,B_906,C_907,D_908) = k7_relat_1(C_907,D_908)
      | ~ m1_subset_1(C_907,k1_zfmisc_1(k2_zfmisc_1(A_905,B_906)))
      | ~ v1_funct_1(C_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15630,plain,(
    ! [D_908] :
      ( k2_partfun1('#skF_1','#skF_1','#skF_4',D_908) = k7_relat_1('#skF_4',D_908)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15206,c_15624])).

tff(c_15637,plain,(
    ! [D_908] : k2_partfun1('#skF_1','#skF_1','#skF_4',D_908) = k7_relat_1('#skF_4',D_908) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15630])).

tff(c_15328,plain,(
    ! [A_857,B_858,C_859,D_860] :
      ( v1_funct_1(k2_partfun1(A_857,B_858,C_859,D_860))
      | ~ m1_subset_1(C_859,k1_zfmisc_1(k2_zfmisc_1(A_857,B_858)))
      | ~ v1_funct_1(C_859) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_15330,plain,(
    ! [D_860] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_860))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15206,c_15328])).

tff(c_15333,plain,(
    ! [D_860] : v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_860)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15330])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15209,plain,(
    ! [A_828] :
      ( A_828 = '#skF_1'
      | ~ r1_tarski(A_828,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15194,c_15194,c_2])).

tff(c_15213,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_15209])).

tff(c_15242,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15213,c_15200,c_15213,c_15213,c_15200,c_15200,c_15213,c_15213,c_15200,c_15200,c_48])).

tff(c_15243,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_15242])).

tff(c_15336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15333,c_15243])).

tff(c_15337,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15242])).

tff(c_15383,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15337])).

tff(c_15639,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15637,c_15383])).

tff(c_15642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15206,c_15350,c_15639])).

tff(c_15643,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_15337])).

tff(c_15644,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15337])).

tff(c_15749,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_15644,c_15742])).

tff(c_28,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_15988,plain,(
    ! [C_944,B_945] :
      ( v1_funct_2(C_944,'#skF_1',B_945)
      | k1_relset_1('#skF_1',B_945,C_944) != '#skF_1'
      | ~ m1_subset_1(C_944,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_945))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15194,c_15194,c_15194,c_15194,c_28])).

tff(c_15994,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1',k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_15644,c_15988])).

tff(c_16000,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15749,c_15994])).

tff(c_16001,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_15643,c_16000])).

tff(c_16160,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16157,c_16001])).

tff(c_16177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15863,c_15350,c_16160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.65/3.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.65/3.79  
% 9.65/3.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.65/3.80  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.65/3.80  
% 9.65/3.80  %Foreground sorts:
% 9.65/3.80  
% 9.65/3.80  
% 9.65/3.80  %Background operators:
% 9.65/3.80  
% 9.65/3.80  
% 9.65/3.80  %Foreground operators:
% 9.65/3.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.65/3.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.65/3.80  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.65/3.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.65/3.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.65/3.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.65/3.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.65/3.80  tff('#skF_2', type, '#skF_2': $i).
% 9.65/3.80  tff('#skF_3', type, '#skF_3': $i).
% 9.65/3.80  tff('#skF_1', type, '#skF_1': $i).
% 9.65/3.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.65/3.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.65/3.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.65/3.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.65/3.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.65/3.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.65/3.80  tff('#skF_4', type, '#skF_4': $i).
% 9.65/3.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.65/3.80  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.65/3.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.65/3.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.65/3.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.65/3.80  
% 9.99/3.82  tff(f_134, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 9.99/3.82  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.99/3.82  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.99/3.82  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.99/3.82  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.99/3.82  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 9.99/3.82  tff(f_102, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.99/3.82  tff(f_96, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.99/3.82  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.99/3.82  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.99/3.82  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.99/3.82  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 9.99/3.82  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.99/3.82  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.99/3.82  tff(c_52, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.99/3.82  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.99/3.82  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.99/3.82  tff(c_62, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.99/3.82  tff(c_65, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_62])).
% 9.99/3.82  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_65])).
% 9.99/3.82  tff(c_50, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.99/3.82  tff(c_59, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 9.99/3.82  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.99/3.82  tff(c_14842, plain, (![A_784, B_785, C_786]: (k1_relset_1(A_784, B_785, C_786)=k1_relat_1(C_786) | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_784, B_785))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.99/3.82  tff(c_14850, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_14842])).
% 9.99/3.82  tff(c_15058, plain, (![B_817, A_818, C_819]: (k1_xboole_0=B_817 | k1_relset_1(A_818, B_817, C_819)=A_818 | ~v1_funct_2(C_819, A_818, B_817) | ~m1_subset_1(C_819, k1_zfmisc_1(k2_zfmisc_1(A_818, B_817))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.99/3.82  tff(c_15067, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_15058])).
% 9.99/3.82  tff(c_15073, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14850, c_15067])).
% 9.99/3.82  tff(c_15074, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_59, c_15073])).
% 9.99/3.82  tff(c_14, plain, (![B_12, A_11]: (k1_relat_1(k7_relat_1(B_12, A_11))=A_11 | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.99/3.82  tff(c_15089, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_15074, c_14])).
% 9.99/3.82  tff(c_15097, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_15089])).
% 9.99/3.82  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.99/3.82  tff(c_14967, plain, (![A_810, B_811, C_812, D_813]: (k2_partfun1(A_810, B_811, C_812, D_813)=k7_relat_1(C_812, D_813) | ~m1_subset_1(C_812, k1_zfmisc_1(k2_zfmisc_1(A_810, B_811))) | ~v1_funct_1(C_812))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.99/3.82  tff(c_14973, plain, (![D_813]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_813)=k7_relat_1('#skF_4', D_813) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_14967])).
% 9.99/3.82  tff(c_14980, plain, (![D_813]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_813)=k7_relat_1('#skF_4', D_813))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14973])).
% 9.99/3.82  tff(c_262, plain, (![A_112, B_113, C_114, D_115]: (k2_partfun1(A_112, B_113, C_114, D_115)=k7_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_1(C_114))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.99/3.82  tff(c_266, plain, (![D_115]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_115)=k7_relat_1('#skF_4', D_115) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_262])).
% 9.99/3.82  tff(c_270, plain, (![D_115]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_115)=k7_relat_1('#skF_4', D_115))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_266])).
% 9.99/3.82  tff(c_550, plain, (![A_145, B_146, C_147, D_148]: (m1_subset_1(k2_partfun1(A_145, B_146, C_147, D_148), k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(C_147))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.99/3.82  tff(c_590, plain, (![D_115]: (m1_subset_1(k7_relat_1('#skF_4', D_115), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_550])).
% 9.99/3.82  tff(c_607, plain, (![D_149]: (m1_subset_1(k7_relat_1('#skF_4', D_149), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_590])).
% 9.99/3.82  tff(c_16, plain, (![C_15, A_13, B_14]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.99/3.82  tff(c_650, plain, (![D_149]: (v1_relat_1(k7_relat_1('#skF_4', D_149)))), inference(resolution, [status(thm)], [c_607, c_16])).
% 9.99/3.82  tff(c_18, plain, (![C_18, B_17, A_16]: (v5_relat_1(C_18, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.99/3.82  tff(c_648, plain, (![D_149]: (v5_relat_1(k7_relat_1('#skF_4', D_149), '#skF_2'))), inference(resolution, [status(thm)], [c_607, c_18])).
% 9.99/3.82  tff(c_8, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.99/3.82  tff(c_194, plain, (![A_92, B_93, C_94, D_95]: (v1_funct_1(k2_partfun1(A_92, B_93, C_94, D_95)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.99/3.82  tff(c_196, plain, (![D_95]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_95)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_194])).
% 9.99/3.82  tff(c_199, plain, (![D_95]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_95)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_196])).
% 9.99/3.82  tff(c_271, plain, (![D_95]: (v1_funct_1(k7_relat_1('#skF_4', D_95)))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_199])).
% 9.99/3.82  tff(c_184, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.99/3.82  tff(c_188, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_184])).
% 9.99/3.82  tff(c_314, plain, (![B_122, A_123, C_124]: (k1_xboole_0=B_122 | k1_relset_1(A_123, B_122, C_124)=A_123 | ~v1_funct_2(C_124, A_123, B_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.99/3.82  tff(c_320, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_314])).
% 9.99/3.82  tff(c_324, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_188, c_320])).
% 9.99/3.82  tff(c_325, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_59, c_324])).
% 9.99/3.82  tff(c_343, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_325, c_14])).
% 9.99/3.82  tff(c_367, plain, (![A_126]: (k1_relat_1(k7_relat_1('#skF_4', A_126))=A_126 | ~r1_tarski(A_126, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_343])).
% 9.99/3.82  tff(c_42, plain, (![B_34, A_33]: (m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_34), A_33))) | ~r1_tarski(k2_relat_1(B_34), A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.99/3.82  tff(c_380, plain, (![A_126, A_33]: (m1_subset_1(k7_relat_1('#skF_4', A_126), k1_zfmisc_1(k2_zfmisc_1(A_126, A_33))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_126)), A_33) | ~v1_funct_1(k7_relat_1('#skF_4', A_126)) | ~v1_relat_1(k7_relat_1('#skF_4', A_126)) | ~r1_tarski(A_126, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_367, c_42])).
% 9.99/3.82  tff(c_404, plain, (![A_126, A_33]: (m1_subset_1(k7_relat_1('#skF_4', A_126), k1_zfmisc_1(k2_zfmisc_1(A_126, A_33))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_126)), A_33) | ~v1_relat_1(k7_relat_1('#skF_4', A_126)) | ~r1_tarski(A_126, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_380])).
% 9.99/3.82  tff(c_14678, plain, (![A_777, A_778]: (m1_subset_1(k7_relat_1('#skF_4', A_777), k1_zfmisc_1(k2_zfmisc_1(A_777, A_778))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_777)), A_778) | ~r1_tarski(A_777, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_404])).
% 9.99/3.82  tff(c_126, plain, (![A_64, B_65, C_66, D_67]: (v1_funct_1(k2_partfun1(A_64, B_65, C_66, D_67)) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.99/3.82  tff(c_128, plain, (![D_67]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_67)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_126])).
% 9.99/3.82  tff(c_131, plain, (![D_67]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_67)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_128])).
% 9.99/3.82  tff(c_48, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.99/3.82  tff(c_69, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 9.99/3.82  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_69])).
% 9.99/3.82  tff(c_135, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_48])).
% 9.99/3.82  tff(c_165, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_135])).
% 9.99/3.82  tff(c_272, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_165])).
% 9.99/3.82  tff(c_14706, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_14678, c_272])).
% 9.99/3.82  tff(c_14772, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14706])).
% 9.99/3.82  tff(c_14793, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_14772])).
% 9.99/3.82  tff(c_14797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_650, c_648, c_14793])).
% 9.99/3.82  tff(c_14798, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_135])).
% 9.99/3.82  tff(c_14990, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14980, c_14798])).
% 9.99/3.82  tff(c_14799, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_135])).
% 9.99/3.82  tff(c_14849, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_14799, c_14842])).
% 9.99/3.82  tff(c_14985, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14980, c_14980, c_14849])).
% 9.99/3.82  tff(c_14989, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14980, c_14799])).
% 9.99/3.82  tff(c_15169, plain, (![B_823, C_824, A_825]: (k1_xboole_0=B_823 | v1_funct_2(C_824, A_825, B_823) | k1_relset_1(A_825, B_823, C_824)!=A_825 | ~m1_subset_1(C_824, k1_zfmisc_1(k2_zfmisc_1(A_825, B_823))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.99/3.82  tff(c_15172, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_14989, c_15169])).
% 9.99/3.82  tff(c_15180, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14985, c_15172])).
% 9.99/3.82  tff(c_15181, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14990, c_59, c_15180])).
% 9.99/3.82  tff(c_15189, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15097, c_15181])).
% 9.99/3.82  tff(c_15193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_15189])).
% 9.99/3.82  tff(c_15194, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_50])).
% 9.99/3.82  tff(c_15195, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 9.99/3.82  tff(c_15200, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15194, c_15195])).
% 9.99/3.82  tff(c_15201, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15200, c_56])).
% 9.99/3.82  tff(c_15206, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15200, c_54])).
% 9.99/3.82  tff(c_15742, plain, (![A_917, B_918, C_919]: (k1_relset_1(A_917, B_918, C_919)=k1_relat_1(C_919) | ~m1_subset_1(C_919, k1_zfmisc_1(k2_zfmisc_1(A_917, B_918))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.99/3.82  tff(c_15750, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_15206, c_15742])).
% 9.99/3.82  tff(c_32, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.99/3.82  tff(c_15852, plain, (![B_934, C_935]: (k1_relset_1('#skF_1', B_934, C_935)='#skF_1' | ~v1_funct_2(C_935, '#skF_1', B_934) | ~m1_subset_1(C_935, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_934))))), inference(demodulation, [status(thm), theory('equality')], [c_15194, c_15194, c_15194, c_15194, c_32])).
% 9.99/3.82  tff(c_15858, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_15206, c_15852])).
% 9.99/3.82  tff(c_15863, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15201, c_15750, c_15858])).
% 9.99/3.82  tff(c_15224, plain, (![B_829, A_830]: (v1_relat_1(B_829) | ~m1_subset_1(B_829, k1_zfmisc_1(A_830)) | ~v1_relat_1(A_830))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.99/3.82  tff(c_15227, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_15206, c_15224])).
% 9.99/3.82  tff(c_15230, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_15227])).
% 9.99/3.82  tff(c_15237, plain, (![C_834, A_835, B_836]: (v4_relat_1(C_834, A_835) | ~m1_subset_1(C_834, k1_zfmisc_1(k2_zfmisc_1(A_835, B_836))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.99/3.82  tff(c_15241, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_15206, c_15237])).
% 9.99/3.82  tff(c_15344, plain, (![B_864, A_865]: (k7_relat_1(B_864, A_865)=B_864 | ~v4_relat_1(B_864, A_865) | ~v1_relat_1(B_864))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.99/3.82  tff(c_15347, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_15241, c_15344])).
% 9.99/3.82  tff(c_15350, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15230, c_15347])).
% 9.99/3.82  tff(c_16139, plain, (![A_958, B_959, C_960, D_961]: (k2_partfun1(A_958, B_959, C_960, D_961)=k7_relat_1(C_960, D_961) | ~m1_subset_1(C_960, k1_zfmisc_1(k2_zfmisc_1(A_958, B_959))) | ~v1_funct_1(C_960))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.99/3.82  tff(c_16147, plain, (![D_961]: (k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_961)=k7_relat_1('#skF_4', D_961) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_15206, c_16139])).
% 9.99/3.82  tff(c_16157, plain, (![D_961]: (k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_961)=k7_relat_1('#skF_4', D_961))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16147])).
% 9.99/3.82  tff(c_15624, plain, (![A_905, B_906, C_907, D_908]: (k2_partfun1(A_905, B_906, C_907, D_908)=k7_relat_1(C_907, D_908) | ~m1_subset_1(C_907, k1_zfmisc_1(k2_zfmisc_1(A_905, B_906))) | ~v1_funct_1(C_907))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.99/3.82  tff(c_15630, plain, (![D_908]: (k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_908)=k7_relat_1('#skF_4', D_908) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_15206, c_15624])).
% 9.99/3.82  tff(c_15637, plain, (![D_908]: (k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_908)=k7_relat_1('#skF_4', D_908))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15630])).
% 9.99/3.82  tff(c_15328, plain, (![A_857, B_858, C_859, D_860]: (v1_funct_1(k2_partfun1(A_857, B_858, C_859, D_860)) | ~m1_subset_1(C_859, k1_zfmisc_1(k2_zfmisc_1(A_857, B_858))) | ~v1_funct_1(C_859))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.99/3.82  tff(c_15330, plain, (![D_860]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_860)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_15206, c_15328])).
% 9.99/3.82  tff(c_15333, plain, (![D_860]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_860)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15330])).
% 9.99/3.82  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.99/3.82  tff(c_15209, plain, (![A_828]: (A_828='#skF_1' | ~r1_tarski(A_828, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15194, c_15194, c_2])).
% 9.99/3.82  tff(c_15213, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_52, c_15209])).
% 9.99/3.82  tff(c_15242, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15213, c_15200, c_15213, c_15213, c_15200, c_15200, c_15213, c_15213, c_15200, c_15200, c_48])).
% 9.99/3.82  tff(c_15243, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_15242])).
% 9.99/3.82  tff(c_15336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15333, c_15243])).
% 9.99/3.82  tff(c_15337, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_15242])).
% 9.99/3.82  tff(c_15383, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_15337])).
% 9.99/3.82  tff(c_15639, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15637, c_15383])).
% 9.99/3.82  tff(c_15642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15206, c_15350, c_15639])).
% 9.99/3.82  tff(c_15643, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_15337])).
% 9.99/3.82  tff(c_15644, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_15337])).
% 9.99/3.82  tff(c_15749, plain, (k1_relset_1('#skF_1', '#skF_1', k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_15644, c_15742])).
% 9.99/3.82  tff(c_28, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.99/3.82  tff(c_15988, plain, (![C_944, B_945]: (v1_funct_2(C_944, '#skF_1', B_945) | k1_relset_1('#skF_1', B_945, C_944)!='#skF_1' | ~m1_subset_1(C_944, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_945))))), inference(demodulation, [status(thm), theory('equality')], [c_15194, c_15194, c_15194, c_15194, c_28])).
% 9.99/3.82  tff(c_15994, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1'), inference(resolution, [status(thm)], [c_15644, c_15988])).
% 9.99/3.82  tff(c_16000, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15749, c_15994])).
% 9.99/3.82  tff(c_16001, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_15643, c_16000])).
% 9.99/3.82  tff(c_16160, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16157, c_16001])).
% 9.99/3.82  tff(c_16177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15863, c_15350, c_16160])).
% 9.99/3.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.82  
% 9.99/3.82  Inference rules
% 9.99/3.82  ----------------------
% 9.99/3.82  #Ref     : 0
% 9.99/3.82  #Sup     : 3788
% 9.99/3.82  #Fact    : 0
% 9.99/3.82  #Define  : 0
% 9.99/3.82  #Split   : 10
% 9.99/3.82  #Chain   : 0
% 9.99/3.82  #Close   : 0
% 9.99/3.82  
% 9.99/3.82  Ordering : KBO
% 9.99/3.82  
% 9.99/3.82  Simplification rules
% 9.99/3.82  ----------------------
% 9.99/3.82  #Subsume      : 908
% 9.99/3.82  #Demod        : 4568
% 9.99/3.82  #Tautology    : 1511
% 9.99/3.82  #SimpNegUnit  : 35
% 9.99/3.82  #BackRed      : 72
% 9.99/3.82  
% 9.99/3.82  #Partial instantiations: 0
% 9.99/3.82  #Strategies tried      : 1
% 9.99/3.82  
% 9.99/3.82  Timing (in seconds)
% 9.99/3.82  ----------------------
% 9.99/3.82  Preprocessing        : 0.34
% 9.99/3.82  Parsing              : 0.18
% 9.99/3.82  CNF conversion       : 0.02
% 9.99/3.82  Main loop            : 2.65
% 9.99/3.82  Inferencing          : 0.77
% 9.99/3.82  Reduction            : 1.12
% 9.99/3.82  Demodulation         : 0.89
% 9.99/3.82  BG Simplification    : 0.08
% 9.99/3.82  Subsumption          : 0.54
% 9.99/3.82  Abstraction          : 0.12
% 9.99/3.82  MUC search           : 0.00
% 9.99/3.82  Cooper               : 0.00
% 9.99/3.82  Total                : 3.04
% 9.99/3.82  Index Insertion      : 0.00
% 9.99/3.82  Index Deletion       : 0.00
% 9.99/3.82  Index Matching       : 0.00
% 9.99/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
