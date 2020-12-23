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
% DateTime   : Thu Dec  3 10:11:44 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 126 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 399 expanded)
%              Number of equality atoms :   47 ( 144 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_292,plain,(
    ! [C_81,B_78,D_77,F_80,E_82,A_79] :
      ( k1_partfun1(A_79,B_78,C_81,D_77,E_82,F_80) = k5_relat_1(E_82,F_80)
      | ~ m1_subset_1(F_80,k1_zfmisc_1(k2_zfmisc_1(C_81,D_77)))
      | ~ v1_funct_1(F_80)
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_1(E_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_294,plain,(
    ! [A_79,B_78,E_82] :
      ( k1_partfun1(A_79,B_78,'#skF_2','#skF_3',E_82,'#skF_5') = k5_relat_1(E_82,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_1(E_82) ) ),
    inference(resolution,[status(thm)],[c_44,c_292])).

tff(c_355,plain,(
    ! [A_89,B_90,E_91] :
      ( k1_partfun1(A_89,B_90,'#skF_2','#skF_3',E_91,'#skF_5') = k5_relat_1(E_91,'#skF_5')
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_1(E_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_294])).

tff(c_364,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_355])).

tff(c_371,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_364])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_383,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_36])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_86,plain,(
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_94,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_89])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_105,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_139,plain,(
    ! [B_57,A_58,C_59] :
      ( k1_xboole_0 = B_57
      | k1_relset_1(A_58,B_57,C_59) = A_58
      | ~ v1_funct_2(C_59,A_58,B_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_142,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_148,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_112,c_142])).

tff(c_149,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_148])).

tff(c_72,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_92,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_96,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_92])).

tff(c_125,plain,(
    ! [B_51,A_52] :
      ( k2_relat_1(k5_relat_1(B_51,A_52)) = k2_relat_1(A_52)
      | ~ r1_tarski(k1_relat_1(A_52),k2_relat_1(B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [A_52] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_52)) = k2_relat_1(A_52)
      | ~ r1_tarski(k1_relat_1(A_52),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_125])).

tff(c_133,plain,(
    ! [A_52] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_52)) = k2_relat_1(A_52)
      | ~ r1_tarski(k1_relat_1(A_52),'#skF_2')
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_128])).

tff(c_160,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_133])).

tff(c_169,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_6,c_94,c_160])).

tff(c_30,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( m1_subset_1(k1_partfun1(A_20,B_21,C_22,D_23,E_24,F_25),k1_zfmisc_1(k2_zfmisc_1(A_20,D_23)))
      | ~ m1_subset_1(F_25,k1_zfmisc_1(k2_zfmisc_1(C_22,D_23)))
      | ~ v1_funct_1(F_25)
      | ~ m1_subset_1(E_24,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_1(E_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_387,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_30])).

tff(c_391,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_44,c_387])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_471,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_391,c_16])).

tff(c_498,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_471])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_383,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:32:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.74  
% 2.86/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.74  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.74  
% 2.86/1.74  %Foreground sorts:
% 2.86/1.74  
% 2.86/1.74  
% 2.86/1.74  %Background operators:
% 2.86/1.74  
% 2.86/1.74  
% 2.86/1.74  %Foreground operators:
% 2.86/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.86/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.74  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.74  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.86/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.74  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.74  
% 3.18/1.76  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 3.18/1.76  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.18/1.76  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.18/1.76  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.18/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.18/1.76  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.18/1.76  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.18/1.76  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.18/1.76  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.18/1.76  tff(f_87, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.18/1.76  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_292, plain, (![C_81, B_78, D_77, F_80, E_82, A_79]: (k1_partfun1(A_79, B_78, C_81, D_77, E_82, F_80)=k5_relat_1(E_82, F_80) | ~m1_subset_1(F_80, k1_zfmisc_1(k2_zfmisc_1(C_81, D_77))) | ~v1_funct_1(F_80) | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_1(E_82))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.18/1.76  tff(c_294, plain, (![A_79, B_78, E_82]: (k1_partfun1(A_79, B_78, '#skF_2', '#skF_3', E_82, '#skF_5')=k5_relat_1(E_82, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_1(E_82))), inference(resolution, [status(thm)], [c_44, c_292])).
% 3.18/1.76  tff(c_355, plain, (![A_89, B_90, E_91]: (k1_partfun1(A_89, B_90, '#skF_2', '#skF_3', E_91, '#skF_5')=k5_relat_1(E_91, '#skF_5') | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_1(E_91))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_294])).
% 3.18/1.76  tff(c_364, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_355])).
% 3.18/1.76  tff(c_371, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_364])).
% 3.18/1.76  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_383, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_371, c_36])).
% 3.18/1.76  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.18/1.76  tff(c_66, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.76  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.18/1.76  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 3.18/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.76  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_86, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.76  tff(c_89, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_86])).
% 3.18/1.76  tff(c_94, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_89])).
% 3.18/1.76  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_105, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.76  tff(c_112, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_105])).
% 3.18/1.76  tff(c_139, plain, (![B_57, A_58, C_59]: (k1_xboole_0=B_57 | k1_relset_1(A_58, B_57, C_59)=A_58 | ~v1_funct_2(C_59, A_58, B_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.18/1.76  tff(c_142, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_139])).
% 3.18/1.76  tff(c_148, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_112, c_142])).
% 3.18/1.76  tff(c_149, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_148])).
% 3.18/1.76  tff(c_72, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_66])).
% 3.18/1.76  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 3.18/1.76  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.18/1.76  tff(c_92, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_86])).
% 3.18/1.76  tff(c_96, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_92])).
% 3.18/1.76  tff(c_125, plain, (![B_51, A_52]: (k2_relat_1(k5_relat_1(B_51, A_52))=k2_relat_1(A_52) | ~r1_tarski(k1_relat_1(A_52), k2_relat_1(B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.76  tff(c_128, plain, (![A_52]: (k2_relat_1(k5_relat_1('#skF_4', A_52))=k2_relat_1(A_52) | ~r1_tarski(k1_relat_1(A_52), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_96, c_125])).
% 3.18/1.76  tff(c_133, plain, (![A_52]: (k2_relat_1(k5_relat_1('#skF_4', A_52))=k2_relat_1(A_52) | ~r1_tarski(k1_relat_1(A_52), '#skF_2') | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_128])).
% 3.18/1.76  tff(c_160, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_149, c_133])).
% 3.18/1.76  tff(c_169, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_6, c_94, c_160])).
% 3.18/1.76  tff(c_30, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1(k1_partfun1(A_20, B_21, C_22, D_23, E_24, F_25), k1_zfmisc_1(k2_zfmisc_1(A_20, D_23))) | ~m1_subset_1(F_25, k1_zfmisc_1(k2_zfmisc_1(C_22, D_23))) | ~v1_funct_1(F_25) | ~m1_subset_1(E_24, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_1(E_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.18/1.76  tff(c_387, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_371, c_30])).
% 3.18/1.76  tff(c_391, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_44, c_387])).
% 3.18/1.76  tff(c_16, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.76  tff(c_471, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_391, c_16])).
% 3.18/1.76  tff(c_498, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_471])).
% 3.18/1.76  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_383, c_498])).
% 3.18/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.76  
% 3.18/1.76  Inference rules
% 3.18/1.76  ----------------------
% 3.18/1.76  #Ref     : 0
% 3.18/1.76  #Sup     : 97
% 3.18/1.76  #Fact    : 0
% 3.18/1.76  #Define  : 0
% 3.18/1.76  #Split   : 5
% 3.18/1.76  #Chain   : 0
% 3.18/1.76  #Close   : 0
% 3.18/1.76  
% 3.18/1.76  Ordering : KBO
% 3.18/1.76  
% 3.18/1.76  Simplification rules
% 3.18/1.76  ----------------------
% 3.18/1.76  #Subsume      : 5
% 3.18/1.76  #Demod        : 71
% 3.18/1.76  #Tautology    : 31
% 3.18/1.76  #SimpNegUnit  : 7
% 3.18/1.76  #BackRed      : 5
% 3.18/1.76  
% 3.18/1.76  #Partial instantiations: 0
% 3.18/1.76  #Strategies tried      : 1
% 3.18/1.76  
% 3.18/1.76  Timing (in seconds)
% 3.18/1.76  ----------------------
% 3.18/1.76  Preprocessing        : 0.53
% 3.18/1.76  Parsing              : 0.27
% 3.18/1.76  CNF conversion       : 0.04
% 3.18/1.76  Main loop            : 0.38
% 3.18/1.76  Inferencing          : 0.13
% 3.18/1.76  Reduction            : 0.13
% 3.18/1.76  Demodulation         : 0.09
% 3.18/1.76  BG Simplification    : 0.03
% 3.18/1.76  Subsumption          : 0.08
% 3.18/1.76  Abstraction          : 0.02
% 3.18/1.76  MUC search           : 0.00
% 3.18/1.76  Cooper               : 0.00
% 3.18/1.76  Total                : 0.95
% 3.18/1.76  Index Insertion      : 0.00
% 3.18/1.76  Index Deletion       : 0.00
% 3.18/1.76  Index Matching       : 0.00
% 3.18/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
