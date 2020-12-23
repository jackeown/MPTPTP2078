%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:41 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 143 expanded)
%              Number of leaves         :   34 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 456 expanded)
%              Number of equality atoms :   46 ( 164 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,B,D) = B
                & k2_relset_1(B,C,E) = C )
             => ( C = k1_xboole_0
                | k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_303,plain,(
    ! [B_87,D_85,A_88,C_84,E_86,F_83] :
      ( k1_partfun1(A_88,B_87,C_84,D_85,E_86,F_83) = k5_relat_1(E_86,F_83)
      | ~ m1_subset_1(F_83,k1_zfmisc_1(k2_zfmisc_1(C_84,D_85)))
      | ~ v1_funct_1(F_83)
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87)))
      | ~ v1_funct_1(E_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_305,plain,(
    ! [A_88,B_87,E_86] :
      ( k1_partfun1(A_88,B_87,'#skF_2','#skF_3',E_86,'#skF_5') = k5_relat_1(E_86,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87)))
      | ~ v1_funct_1(E_86) ) ),
    inference(resolution,[status(thm)],[c_44,c_303])).

tff(c_415,plain,(
    ! [A_100,B_101,E_102] :
      ( k1_partfun1(A_100,B_101,'#skF_2','#skF_3',E_102,'#skF_5') = k5_relat_1(E_102,'#skF_5')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(E_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_305])).

tff(c_424,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_415])).

tff(c_431,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_424])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_526,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_36])).

tff(c_63,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_63])).

tff(c_78,plain,(
    ! [C_41,B_42,A_43] :
      ( v5_relat_1(C_41,B_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_78])).

tff(c_71,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_63])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_97,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_97])).

tff(c_107,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_103])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_1] :
      ( r1_tarski('#skF_2',A_1)
      | ~ v5_relat_1('#skF_4',A_1)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_153,plain,(
    ! [A_54] :
      ( r1_tarski('#skF_2',A_54)
      | ~ v5_relat_1('#skF_4',A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_128])).

tff(c_157,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_153])).

tff(c_40,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_100,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_97])).

tff(c_105,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_100])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_136,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_136])).

tff(c_201,plain,(
    ! [B_71,A_72,C_73] :
      ( k1_xboole_0 = B_71
      | k1_relset_1(A_72,B_71,C_73) = A_72
      | ~ v1_funct_2(C_73,A_72,B_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_201])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_143,c_204])).

tff(c_211,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_210])).

tff(c_175,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(k5_relat_1(B_62,A_63)) = k2_relat_1(A_63)
      | ~ r1_tarski(k1_relat_1(A_63),k2_relat_1(B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_178,plain,(
    ! [A_63] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_63)) = k2_relat_1(A_63)
      | ~ r1_tarski(k1_relat_1(A_63),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_175])).

tff(c_183,plain,(
    ! [A_63] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_63)) = k2_relat_1(A_63)
      | ~ r1_tarski(k1_relat_1(A_63),'#skF_2')
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_178])).

tff(c_222,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_183])).

tff(c_231,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_157,c_105,c_222])).

tff(c_30,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] :
      ( m1_subset_1(k1_partfun1(A_21,B_22,C_23,D_24,E_25,F_26),k1_zfmisc_1(k2_zfmisc_1(A_21,D_24)))
      | ~ m1_subset_1(F_26,k1_zfmisc_1(k2_zfmisc_1(C_23,D_24)))
      | ~ v1_funct_1(F_26)
      | ~ m1_subset_1(E_25,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(E_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_530,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_30])).

tff(c_534,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_44,c_530])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_564,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_534,c_16])).

tff(c_600,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_564])).

tff(c_602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:31:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.37  
% 2.92/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.92/1.37  
% 2.92/1.37  %Foreground sorts:
% 2.92/1.37  
% 2.92/1.37  
% 2.92/1.37  %Background operators:
% 2.92/1.37  
% 2.92/1.37  
% 2.92/1.37  %Foreground operators:
% 2.92/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.92/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.92/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.37  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.92/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.92/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.92/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.92/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.37  
% 2.92/1.39  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 2.92/1.39  tff(f_98, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.92/1.39  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.92/1.39  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.92/1.39  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.92/1.39  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.92/1.39  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.92/1.39  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.92/1.39  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.92/1.39  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.92/1.39  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_303, plain, (![B_87, D_85, A_88, C_84, E_86, F_83]: (k1_partfun1(A_88, B_87, C_84, D_85, E_86, F_83)=k5_relat_1(E_86, F_83) | ~m1_subset_1(F_83, k1_zfmisc_1(k2_zfmisc_1(C_84, D_85))) | ~v1_funct_1(F_83) | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))) | ~v1_funct_1(E_86))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.92/1.39  tff(c_305, plain, (![A_88, B_87, E_86]: (k1_partfun1(A_88, B_87, '#skF_2', '#skF_3', E_86, '#skF_5')=k5_relat_1(E_86, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))) | ~v1_funct_1(E_86))), inference(resolution, [status(thm)], [c_44, c_303])).
% 2.92/1.39  tff(c_415, plain, (![A_100, B_101, E_102]: (k1_partfun1(A_100, B_101, '#skF_2', '#skF_3', E_102, '#skF_5')=k5_relat_1(E_102, '#skF_5') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_1(E_102))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_305])).
% 2.92/1.39  tff(c_424, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_415])).
% 2.92/1.39  tff(c_431, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_424])).
% 2.92/1.39  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_526, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_431, c_36])).
% 2.92/1.39  tff(c_63, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.39  tff(c_70, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_63])).
% 2.92/1.39  tff(c_78, plain, (![C_41, B_42, A_43]: (v5_relat_1(C_41, B_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.92/1.39  tff(c_86, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_78])).
% 2.92/1.39  tff(c_71, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_63])).
% 2.92/1.39  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_97, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.92/1.39  tff(c_103, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_97])).
% 2.92/1.39  tff(c_107, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_103])).
% 2.92/1.39  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.39  tff(c_128, plain, (![A_1]: (r1_tarski('#skF_2', A_1) | ~v5_relat_1('#skF_4', A_1) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 2.92/1.39  tff(c_153, plain, (![A_54]: (r1_tarski('#skF_2', A_54) | ~v5_relat_1('#skF_4', A_54))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_128])).
% 2.92/1.39  tff(c_157, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_86, c_153])).
% 2.92/1.39  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_100, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_97])).
% 2.92/1.39  tff(c_105, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_100])).
% 2.92/1.39  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.92/1.39  tff(c_136, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.92/1.39  tff(c_143, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_136])).
% 2.92/1.39  tff(c_201, plain, (![B_71, A_72, C_73]: (k1_xboole_0=B_71 | k1_relset_1(A_72, B_71, C_73)=A_72 | ~v1_funct_2(C_73, A_72, B_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.92/1.39  tff(c_204, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_201])).
% 2.92/1.39  tff(c_210, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_143, c_204])).
% 2.92/1.39  tff(c_211, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_210])).
% 2.92/1.39  tff(c_175, plain, (![B_62, A_63]: (k2_relat_1(k5_relat_1(B_62, A_63))=k2_relat_1(A_63) | ~r1_tarski(k1_relat_1(A_63), k2_relat_1(B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.92/1.39  tff(c_178, plain, (![A_63]: (k2_relat_1(k5_relat_1('#skF_4', A_63))=k2_relat_1(A_63) | ~r1_tarski(k1_relat_1(A_63), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_107, c_175])).
% 2.92/1.39  tff(c_183, plain, (![A_63]: (k2_relat_1(k5_relat_1('#skF_4', A_63))=k2_relat_1(A_63) | ~r1_tarski(k1_relat_1(A_63), '#skF_2') | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_178])).
% 2.92/1.39  tff(c_222, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_211, c_183])).
% 2.92/1.39  tff(c_231, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_157, c_105, c_222])).
% 2.92/1.39  tff(c_30, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (m1_subset_1(k1_partfun1(A_21, B_22, C_23, D_24, E_25, F_26), k1_zfmisc_1(k2_zfmisc_1(A_21, D_24))) | ~m1_subset_1(F_26, k1_zfmisc_1(k2_zfmisc_1(C_23, D_24))) | ~v1_funct_1(F_26) | ~m1_subset_1(E_25, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(E_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.92/1.39  tff(c_530, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_431, c_30])).
% 2.92/1.39  tff(c_534, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_44, c_530])).
% 2.92/1.39  tff(c_16, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.92/1.39  tff(c_564, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_534, c_16])).
% 2.92/1.39  tff(c_600, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_231, c_564])).
% 2.92/1.39  tff(c_602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_526, c_600])).
% 2.92/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.39  
% 2.92/1.39  Inference rules
% 2.92/1.39  ----------------------
% 2.92/1.39  #Ref     : 0
% 2.92/1.39  #Sup     : 122
% 2.92/1.39  #Fact    : 0
% 2.92/1.39  #Define  : 0
% 2.92/1.39  #Split   : 6
% 2.92/1.39  #Chain   : 0
% 2.92/1.39  #Close   : 0
% 2.92/1.39  
% 2.92/1.39  Ordering : KBO
% 2.92/1.39  
% 2.92/1.39  Simplification rules
% 2.92/1.39  ----------------------
% 2.92/1.39  #Subsume      : 6
% 2.92/1.39  #Demod        : 73
% 2.92/1.39  #Tautology    : 32
% 2.92/1.39  #SimpNegUnit  : 7
% 2.92/1.39  #BackRed      : 5
% 2.92/1.39  
% 2.92/1.39  #Partial instantiations: 0
% 2.92/1.39  #Strategies tried      : 1
% 2.92/1.39  
% 2.92/1.39  Timing (in seconds)
% 2.92/1.39  ----------------------
% 2.92/1.39  Preprocessing        : 0.32
% 2.92/1.39  Parsing              : 0.17
% 2.92/1.39  CNF conversion       : 0.02
% 2.92/1.39  Main loop            : 0.32
% 2.92/1.39  Inferencing          : 0.11
% 2.92/1.39  Reduction            : 0.10
% 2.92/1.39  Demodulation         : 0.07
% 2.92/1.39  BG Simplification    : 0.02
% 2.92/1.39  Subsumption          : 0.06
% 2.92/1.39  Abstraction          : 0.02
% 2.92/1.39  MUC search           : 0.00
% 2.92/1.39  Cooper               : 0.00
% 2.92/1.39  Total                : 0.67
% 2.92/1.39  Index Insertion      : 0.00
% 2.92/1.39  Index Deletion       : 0.00
% 2.92/1.39  Index Matching       : 0.00
% 2.92/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
