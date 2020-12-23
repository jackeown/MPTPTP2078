%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:59 EST 2020

% Result     : Theorem 9.32s
% Output     : CNFRefutation 9.32s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 320 expanded)
%              Number of leaves         :   38 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          :  257 (1231 expanded)
%              Number of equality atoms :   60 ( 310 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_147,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_155,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_147])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_160,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_50])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_79])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_85])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_109,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_117,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_109])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_720,plain,(
    ! [E_121,A_122,D_119,F_123,B_120,C_124] :
      ( k1_partfun1(A_122,B_120,C_124,D_119,E_121,F_123) = k5_relat_1(E_121,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_124,D_119)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_728,plain,(
    ! [A_122,B_120,E_121] :
      ( k1_partfun1(A_122,B_120,'#skF_2','#skF_3',E_121,'#skF_5') = k5_relat_1(E_121,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(resolution,[status(thm)],[c_58,c_720])).

tff(c_875,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_2','#skF_3',E_142,'#skF_5') = k5_relat_1(E_142,'#skF_5')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_728])).

tff(c_893,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_875])).

tff(c_907,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_893])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_995,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_56])).

tff(c_38,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_999,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_38])).

tff(c_1003,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_999])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1030,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1003,c_24])).

tff(c_1065,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_1030])).

tff(c_82,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_79])).

tff(c_88,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_54,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_130,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_137,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_130])).

tff(c_257,plain,(
    ! [B_85,A_86,C_87] :
      ( k1_xboole_0 = B_85
      | k1_relset_1(A_86,B_85,C_87) = A_86
      | ~ v1_funct_2(C_87,A_86,B_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_257])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_137,c_263])).

tff(c_271,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_270])).

tff(c_480,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(k1_relat_1(A_99),k2_relat_1(B_100))
      | ~ v2_funct_1(A_99)
      | k2_relat_1(k5_relat_1(B_100,A_99)) != k2_relat_1(A_99)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_491,plain,(
    ! [B_100] :
      ( r1_tarski('#skF_2',k2_relat_1(B_100))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_100,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_480])).

tff(c_563,plain,(
    ! [B_104] :
      ( r1_tarski('#skF_2',k2_relat_1(B_104))
      | k2_relat_1(k5_relat_1(B_104,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_54,c_491])).

tff(c_101,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k2_relat_1(B_50),A_51)
      | ~ v5_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [B_50,A_51] :
      ( k2_relat_1(B_50) = A_51
      | ~ r1_tarski(A_51,k2_relat_1(B_50))
      | ~ v5_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_6290,plain,(
    ! [B_429] :
      ( k2_relat_1(B_429) = '#skF_2'
      | ~ v5_relat_1(B_429,'#skF_2')
      | k2_relat_1(k5_relat_1(B_429,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_429)
      | ~ v1_relat_1(B_429) ) ),
    inference(resolution,[status(thm)],[c_563,c_104])).

tff(c_6293,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | k2_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_6290])).

tff(c_6295,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_117,c_6293])).

tff(c_6296,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_6295])).

tff(c_116,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_109])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [B_38,A_37] :
      ( m1_subset_1(B_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_38),A_37)))
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1815,plain,(
    ! [B_191,E_193,B_190,A_192,A_189] :
      ( k1_partfun1(A_192,B_191,k1_relat_1(B_190),A_189,E_193,B_190) = k5_relat_1(E_193,B_190)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191)))
      | ~ v1_funct_1(E_193)
      | ~ r1_tarski(k2_relat_1(B_190),A_189)
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(resolution,[status(thm)],[c_44,c_720])).

tff(c_1835,plain,(
    ! [B_190,A_189] :
      ( k1_partfun1('#skF_1','#skF_2',k1_relat_1(B_190),A_189,'#skF_4',B_190) = k5_relat_1('#skF_4',B_190)
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k2_relat_1(B_190),A_189)
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(resolution,[status(thm)],[c_64,c_1815])).

tff(c_3164,plain,(
    ! [B_312,A_313] :
      ( k1_partfun1('#skF_1','#skF_2',k1_relat_1(B_312),A_313,'#skF_4',B_312) = k5_relat_1('#skF_4',B_312)
      | ~ r1_tarski(k2_relat_1(B_312),A_313)
      | ~ v1_funct_1(B_312)
      | ~ v1_relat_1(B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1835])).

tff(c_6498,plain,(
    ! [B_441] :
      ( k1_partfun1('#skF_1','#skF_2',k1_relat_1(B_441),k2_relat_1(B_441),'#skF_4',B_441) = k5_relat_1('#skF_4',B_441)
      | ~ v1_funct_1(B_441)
      | ~ v1_relat_1(B_441) ) ),
    inference(resolution,[status(thm)],[c_6,c_3164])).

tff(c_801,plain,(
    ! [F_135,A_133,B_136,E_137,D_132,C_134] :
      ( m1_subset_1(k1_partfun1(A_133,B_136,C_134,D_132,E_137,F_135),k1_zfmisc_1(k2_zfmisc_1(A_133,D_132)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_134,D_132)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_133,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( v5_relat_1(C_15,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1566,plain,(
    ! [D_171,E_170,C_167,F_172,A_168,B_169] :
      ( v5_relat_1(k1_partfun1(A_168,B_169,C_167,D_171,E_170,F_172),D_171)
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_167,D_171)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_1(E_170) ) ),
    inference(resolution,[status(thm)],[c_801,c_18])).

tff(c_1606,plain,(
    ! [B_38,A_37,E_170,A_168,B_169] :
      ( v5_relat_1(k1_partfun1(A_168,B_169,k1_relat_1(B_38),A_37,E_170,B_38),A_37)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_1(E_170)
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_44,c_1566])).

tff(c_6516,plain,(
    ! [B_441] :
      ( v5_relat_1(k5_relat_1('#skF_4',B_441),k2_relat_1(B_441))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k2_relat_1(B_441),k2_relat_1(B_441))
      | ~ v1_funct_1(B_441)
      | ~ v1_relat_1(B_441)
      | ~ v1_funct_1(B_441)
      | ~ v1_relat_1(B_441) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6498,c_1606])).

tff(c_6568,plain,(
    ! [B_445] :
      ( v5_relat_1(k5_relat_1('#skF_4',B_445),k2_relat_1(B_445))
      | ~ v1_funct_1(B_445)
      | ~ v1_relat_1(B_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_68,c_64,c_6516])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1042,plain,
    ( v1_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1003,c_8])).

tff(c_1071,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1042])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,(
    ! [B_65,A_66] :
      ( k2_relat_1(B_65) = A_66
      | ~ r1_tarski(A_66,k2_relat_1(B_65))
      | ~ v5_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_3331,plain,(
    ! [B_315,B_314] :
      ( k2_relat_1(B_315) = k2_relat_1(B_314)
      | ~ v5_relat_1(B_315,k2_relat_1(B_314))
      | ~ v1_relat_1(B_315)
      | ~ v5_relat_1(B_314,k2_relat_1(B_315))
      | ~ v1_relat_1(B_314) ) ),
    inference(resolution,[status(thm)],[c_12,c_165])).

tff(c_3336,plain,(
    ! [B_315] :
      ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(B_315)
      | ~ v5_relat_1(B_315,'#skF_3')
      | ~ v1_relat_1(B_315)
      | ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(B_315))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_3331])).

tff(c_3347,plain,(
    ! [B_315] :
      ( k2_relat_1(B_315) = '#skF_3'
      | ~ v5_relat_1(B_315,'#skF_3')
      | ~ v1_relat_1(B_315)
      | ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(B_315)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_1065,c_3336])).

tff(c_6572,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6568,c_3347])).

tff(c_6588,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_116,c_6572])).

tff(c_6590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6296,c_6588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.32/3.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.42  
% 9.32/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.32/3.42  
% 9.32/3.42  %Foreground sorts:
% 9.32/3.42  
% 9.32/3.42  
% 9.32/3.42  %Background operators:
% 9.32/3.42  
% 9.32/3.42  
% 9.32/3.42  %Foreground operators:
% 9.32/3.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.32/3.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.32/3.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.32/3.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.32/3.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.32/3.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.32/3.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.32/3.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.32/3.42  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.32/3.42  tff('#skF_5', type, '#skF_5': $i).
% 9.32/3.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.32/3.42  tff('#skF_2', type, '#skF_2': $i).
% 9.32/3.42  tff('#skF_3', type, '#skF_3': $i).
% 9.32/3.42  tff('#skF_1', type, '#skF_1': $i).
% 9.32/3.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.32/3.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.32/3.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.32/3.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.32/3.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.32/3.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.32/3.42  tff('#skF_4', type, '#skF_4': $i).
% 9.32/3.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.32/3.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.32/3.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.32/3.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.32/3.42  
% 9.32/3.44  tff(f_149, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 9.32/3.44  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.32/3.44  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.32/3.44  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.32/3.44  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.32/3.44  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.32/3.44  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.32/3.44  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.32/3.44  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.32/3.44  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 9.32/3.44  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.32/3.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.32/3.44  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.32/3.44  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_147, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.32/3.44  tff(c_155, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_147])).
% 9.32/3.44  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_160, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_50])).
% 9.32/3.44  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.32/3.44  tff(c_79, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.32/3.44  tff(c_85, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_79])).
% 9.32/3.44  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_85])).
% 9.32/3.44  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_109, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.44  tff(c_117, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_109])).
% 9.32/3.44  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_720, plain, (![E_121, A_122, D_119, F_123, B_120, C_124]: (k1_partfun1(A_122, B_120, C_124, D_119, E_121, F_123)=k5_relat_1(E_121, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_124, D_119))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_120))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.32/3.44  tff(c_728, plain, (![A_122, B_120, E_121]: (k1_partfun1(A_122, B_120, '#skF_2', '#skF_3', E_121, '#skF_5')=k5_relat_1(E_121, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_120))) | ~v1_funct_1(E_121))), inference(resolution, [status(thm)], [c_58, c_720])).
% 9.32/3.44  tff(c_875, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_2', '#skF_3', E_142, '#skF_5')=k5_relat_1(E_142, '#skF_5') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_728])).
% 9.32/3.44  tff(c_893, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_875])).
% 9.32/3.44  tff(c_907, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_893])).
% 9.32/3.44  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_995, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_907, c_56])).
% 9.32/3.44  tff(c_38, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.32/3.44  tff(c_999, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_907, c_38])).
% 9.32/3.44  tff(c_1003, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_999])).
% 9.32/3.44  tff(c_24, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.32/3.44  tff(c_1030, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1003, c_24])).
% 9.32/3.44  tff(c_1065, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_995, c_1030])).
% 9.32/3.44  tff(c_82, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_79])).
% 9.32/3.44  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 9.32/3.44  tff(c_54, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.32/3.44  tff(c_130, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.32/3.44  tff(c_137, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_130])).
% 9.32/3.44  tff(c_257, plain, (![B_85, A_86, C_87]: (k1_xboole_0=B_85 | k1_relset_1(A_86, B_85, C_87)=A_86 | ~v1_funct_2(C_87, A_86, B_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.32/3.44  tff(c_263, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_257])).
% 9.32/3.44  tff(c_270, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_137, c_263])).
% 9.32/3.44  tff(c_271, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_270])).
% 9.32/3.44  tff(c_480, plain, (![A_99, B_100]: (r1_tarski(k1_relat_1(A_99), k2_relat_1(B_100)) | ~v2_funct_1(A_99) | k2_relat_1(k5_relat_1(B_100, A_99))!=k2_relat_1(A_99) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.32/3.44  tff(c_491, plain, (![B_100]: (r1_tarski('#skF_2', k2_relat_1(B_100)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_100, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_100) | ~v1_relat_1(B_100) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_271, c_480])).
% 9.32/3.44  tff(c_563, plain, (![B_104]: (r1_tarski('#skF_2', k2_relat_1(B_104)) | k2_relat_1(k5_relat_1(B_104, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_54, c_491])).
% 9.32/3.44  tff(c_101, plain, (![B_50, A_51]: (r1_tarski(k2_relat_1(B_50), A_51) | ~v5_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.32/3.44  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.32/3.44  tff(c_104, plain, (![B_50, A_51]: (k2_relat_1(B_50)=A_51 | ~r1_tarski(A_51, k2_relat_1(B_50)) | ~v5_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_101, c_2])).
% 9.32/3.44  tff(c_6290, plain, (![B_429]: (k2_relat_1(B_429)='#skF_2' | ~v5_relat_1(B_429, '#skF_2') | k2_relat_1(k5_relat_1(B_429, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_429) | ~v1_relat_1(B_429))), inference(resolution, [status(thm)], [c_563, c_104])).
% 9.32/3.44  tff(c_6293, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | k2_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1065, c_6290])).
% 9.32/3.44  tff(c_6295, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_68, c_117, c_6293])).
% 9.32/3.44  tff(c_6296, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_160, c_6295])).
% 9.32/3.44  tff(c_116, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_109])).
% 9.32/3.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.32/3.44  tff(c_44, plain, (![B_38, A_37]: (m1_subset_1(B_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_38), A_37))) | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.32/3.44  tff(c_1815, plain, (![B_191, E_193, B_190, A_192, A_189]: (k1_partfun1(A_192, B_191, k1_relat_1(B_190), A_189, E_193, B_190)=k5_relat_1(E_193, B_190) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))) | ~v1_funct_1(E_193) | ~r1_tarski(k2_relat_1(B_190), A_189) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(resolution, [status(thm)], [c_44, c_720])).
% 9.32/3.44  tff(c_1835, plain, (![B_190, A_189]: (k1_partfun1('#skF_1', '#skF_2', k1_relat_1(B_190), A_189, '#skF_4', B_190)=k5_relat_1('#skF_4', B_190) | ~v1_funct_1('#skF_4') | ~r1_tarski(k2_relat_1(B_190), A_189) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(resolution, [status(thm)], [c_64, c_1815])).
% 9.32/3.44  tff(c_3164, plain, (![B_312, A_313]: (k1_partfun1('#skF_1', '#skF_2', k1_relat_1(B_312), A_313, '#skF_4', B_312)=k5_relat_1('#skF_4', B_312) | ~r1_tarski(k2_relat_1(B_312), A_313) | ~v1_funct_1(B_312) | ~v1_relat_1(B_312))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1835])).
% 9.32/3.44  tff(c_6498, plain, (![B_441]: (k1_partfun1('#skF_1', '#skF_2', k1_relat_1(B_441), k2_relat_1(B_441), '#skF_4', B_441)=k5_relat_1('#skF_4', B_441) | ~v1_funct_1(B_441) | ~v1_relat_1(B_441))), inference(resolution, [status(thm)], [c_6, c_3164])).
% 9.32/3.44  tff(c_801, plain, (![F_135, A_133, B_136, E_137, D_132, C_134]: (m1_subset_1(k1_partfun1(A_133, B_136, C_134, D_132, E_137, F_135), k1_zfmisc_1(k2_zfmisc_1(A_133, D_132))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_134, D_132))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_133, B_136))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.32/3.44  tff(c_18, plain, (![C_15, B_14, A_13]: (v5_relat_1(C_15, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.44  tff(c_1566, plain, (![D_171, E_170, C_167, F_172, A_168, B_169]: (v5_relat_1(k1_partfun1(A_168, B_169, C_167, D_171, E_170, F_172), D_171) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_167, D_171))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_1(E_170))), inference(resolution, [status(thm)], [c_801, c_18])).
% 9.32/3.44  tff(c_1606, plain, (![B_38, A_37, E_170, A_168, B_169]: (v5_relat_1(k1_partfun1(A_168, B_169, k1_relat_1(B_38), A_37, E_170, B_38), A_37) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_1(E_170) | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_44, c_1566])).
% 9.32/3.44  tff(c_6516, plain, (![B_441]: (v5_relat_1(k5_relat_1('#skF_4', B_441), k2_relat_1(B_441)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4') | ~r1_tarski(k2_relat_1(B_441), k2_relat_1(B_441)) | ~v1_funct_1(B_441) | ~v1_relat_1(B_441) | ~v1_funct_1(B_441) | ~v1_relat_1(B_441))), inference(superposition, [status(thm), theory('equality')], [c_6498, c_1606])).
% 9.32/3.44  tff(c_6568, plain, (![B_445]: (v5_relat_1(k5_relat_1('#skF_4', B_445), k2_relat_1(B_445)) | ~v1_funct_1(B_445) | ~v1_relat_1(B_445))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_68, c_64, c_6516])).
% 9.32/3.44  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.32/3.44  tff(c_1042, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1003, c_8])).
% 9.32/3.44  tff(c_1071, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1042])).
% 9.32/3.44  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.32/3.44  tff(c_165, plain, (![B_65, A_66]: (k2_relat_1(B_65)=A_66 | ~r1_tarski(A_66, k2_relat_1(B_65)) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_101, c_2])).
% 9.32/3.44  tff(c_3331, plain, (![B_315, B_314]: (k2_relat_1(B_315)=k2_relat_1(B_314) | ~v5_relat_1(B_315, k2_relat_1(B_314)) | ~v1_relat_1(B_315) | ~v5_relat_1(B_314, k2_relat_1(B_315)) | ~v1_relat_1(B_314))), inference(resolution, [status(thm)], [c_12, c_165])).
% 9.32/3.44  tff(c_3336, plain, (![B_315]: (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(B_315) | ~v5_relat_1(B_315, '#skF_3') | ~v1_relat_1(B_315) | ~v5_relat_1(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1(B_315)) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1065, c_3331])).
% 9.32/3.44  tff(c_3347, plain, (![B_315]: (k2_relat_1(B_315)='#skF_3' | ~v5_relat_1(B_315, '#skF_3') | ~v1_relat_1(B_315) | ~v5_relat_1(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1(B_315)))), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_1065, c_3336])).
% 9.32/3.44  tff(c_6572, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6568, c_3347])).
% 9.32/3.44  tff(c_6588, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_116, c_6572])).
% 9.32/3.44  tff(c_6590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6296, c_6588])).
% 9.32/3.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.44  
% 9.32/3.44  Inference rules
% 9.32/3.44  ----------------------
% 9.32/3.44  #Ref     : 0
% 9.32/3.44  #Sup     : 1318
% 9.32/3.44  #Fact    : 0
% 9.32/3.44  #Define  : 0
% 9.32/3.44  #Split   : 17
% 9.32/3.44  #Chain   : 0
% 9.32/3.44  #Close   : 0
% 9.32/3.44  
% 9.32/3.44  Ordering : KBO
% 9.32/3.44  
% 9.32/3.44  Simplification rules
% 9.32/3.44  ----------------------
% 9.32/3.44  #Subsume      : 49
% 9.32/3.44  #Demod        : 1761
% 9.32/3.44  #Tautology    : 340
% 9.32/3.44  #SimpNegUnit  : 54
% 9.32/3.44  #BackRed      : 77
% 9.32/3.44  
% 9.32/3.44  #Partial instantiations: 0
% 9.32/3.44  #Strategies tried      : 1
% 9.32/3.44  
% 9.32/3.44  Timing (in seconds)
% 9.32/3.44  ----------------------
% 9.32/3.45  Preprocessing        : 0.35
% 9.32/3.45  Parsing              : 0.18
% 9.32/3.45  CNF conversion       : 0.02
% 9.32/3.45  Main loop            : 2.32
% 9.32/3.45  Inferencing          : 0.67
% 9.32/3.45  Reduction            : 1.02
% 9.32/3.45  Demodulation         : 0.78
% 9.32/3.45  BG Simplification    : 0.05
% 9.32/3.45  Subsumption          : 0.42
% 9.32/3.45  Abstraction          : 0.07
% 9.32/3.45  MUC search           : 0.00
% 9.32/3.45  Cooper               : 0.00
% 9.32/3.45  Total                : 2.71
% 9.32/3.45  Index Insertion      : 0.00
% 9.32/3.45  Index Deletion       : 0.00
% 9.32/3.45  Index Matching       : 0.00
% 9.32/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
