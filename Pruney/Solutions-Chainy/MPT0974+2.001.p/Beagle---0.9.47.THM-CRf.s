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
% DateTime   : Thu Dec  3 10:11:41 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 110 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 340 expanded)
%              Number of equality atoms :   29 ( 114 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_98,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_49,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_73,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_26,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_82,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_90,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_88,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_92,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_88])).

tff(c_101,plain,(
    ! [B_44,A_45] :
      ( k2_relat_1(k5_relat_1(B_44,A_45)) = k2_relat_1(A_45)
      | ~ r1_tarski(k1_relat_1(A_45),k2_relat_1(B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    ! [A_45] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_45)) = k2_relat_1(A_45)
      | ~ r1_tarski(k1_relat_1(A_45),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_101])).

tff(c_128,plain,(
    ! [A_52] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_52)) = k2_relat_1(A_52)
      | ~ r1_tarski(k1_relat_1(A_52),'#skF_2')
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_104])).

tff(c_133,plain,(
    ! [B_2] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_2)) = k2_relat_1(B_2)
      | ~ v4_relat_1(B_2,'#skF_2')
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_207,plain,(
    ! [F_67,B_68,E_69,C_66,D_65,A_64] :
      ( k1_partfun1(A_64,B_68,C_66,D_65,E_69,F_67) = k5_relat_1(E_69,F_67)
      | ~ m1_subset_1(F_67,k1_zfmisc_1(k2_zfmisc_1(C_66,D_65)))
      | ~ v1_funct_1(F_67)
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_64,B_68)))
      | ~ v1_funct_1(E_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_209,plain,(
    ! [A_64,B_68,E_69] :
      ( k1_partfun1(A_64,B_68,'#skF_2','#skF_3',E_69,'#skF_5') = k5_relat_1(E_69,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_64,B_68)))
      | ~ v1_funct_1(E_69) ) ),
    inference(resolution,[status(thm)],[c_30,c_207])).

tff(c_218,plain,(
    ! [A_70,B_71,E_72] :
      ( k1_partfun1(A_70,B_71,'#skF_2','#skF_3',E_72,'#skF_5') = k5_relat_1(E_72,'#skF_5')
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_1(E_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_209])).

tff(c_224,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_230,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_224])).

tff(c_255,plain,(
    ! [B_78,D_77,F_79,E_80,A_81,C_76] :
      ( m1_subset_1(k1_partfun1(A_81,B_78,C_76,D_77,E_80,F_79),k1_zfmisc_1(k2_zfmisc_1(A_81,D_77)))
      | ~ m1_subset_1(F_79,k1_zfmisc_1(k2_zfmisc_1(C_76,D_77)))
      | ~ v1_funct_1(F_79)
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_78)))
      | ~ v1_funct_1(E_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_286,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_255])).

tff(c_301,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_30,c_286])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_350,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_301,c_14])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_237,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_22])).

tff(c_720,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_237])).

tff(c_761,plain,
    ( k2_relat_1('#skF_5') != '#skF_3'
    | ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_720])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_80,c_90,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.60  
% 3.10/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.10/1.60  
% 3.10/1.60  %Foreground sorts:
% 3.10/1.60  
% 3.10/1.60  
% 3.10/1.60  %Background operators:
% 3.10/1.60  
% 3.10/1.60  
% 3.10/1.60  %Foreground operators:
% 3.10/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.10/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.10/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.60  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.60  
% 3.10/1.62  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 3.10/1.62  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.10/1.62  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.62  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.62  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.10/1.62  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.10/1.62  tff(f_76, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.10/1.62  tff(f_66, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.10/1.62  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.62  tff(c_49, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.10/1.62  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_49])).
% 3.10/1.62  tff(c_73, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.10/1.62  tff(c_80, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_73])).
% 3.10/1.62  tff(c_26, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.62  tff(c_82, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.10/1.62  tff(c_85, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_82])).
% 3.10/1.62  tff(c_90, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_85])).
% 3.10/1.62  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.62  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.62  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_49])).
% 3.10/1.62  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.62  tff(c_88, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_82])).
% 3.10/1.62  tff(c_92, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_88])).
% 3.10/1.62  tff(c_101, plain, (![B_44, A_45]: (k2_relat_1(k5_relat_1(B_44, A_45))=k2_relat_1(A_45) | ~r1_tarski(k1_relat_1(A_45), k2_relat_1(B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.10/1.62  tff(c_104, plain, (![A_45]: (k2_relat_1(k5_relat_1('#skF_4', A_45))=k2_relat_1(A_45) | ~r1_tarski(k1_relat_1(A_45), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_92, c_101])).
% 3.10/1.62  tff(c_128, plain, (![A_52]: (k2_relat_1(k5_relat_1('#skF_4', A_52))=k2_relat_1(A_52) | ~r1_tarski(k1_relat_1(A_52), '#skF_2') | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_104])).
% 3.10/1.62  tff(c_133, plain, (![B_2]: (k2_relat_1(k5_relat_1('#skF_4', B_2))=k2_relat_1(B_2) | ~v4_relat_1(B_2, '#skF_2') | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_128])).
% 3.10/1.62  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.62  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.62  tff(c_207, plain, (![F_67, B_68, E_69, C_66, D_65, A_64]: (k1_partfun1(A_64, B_68, C_66, D_65, E_69, F_67)=k5_relat_1(E_69, F_67) | ~m1_subset_1(F_67, k1_zfmisc_1(k2_zfmisc_1(C_66, D_65))) | ~v1_funct_1(F_67) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_64, B_68))) | ~v1_funct_1(E_69))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.10/1.62  tff(c_209, plain, (![A_64, B_68, E_69]: (k1_partfun1(A_64, B_68, '#skF_2', '#skF_3', E_69, '#skF_5')=k5_relat_1(E_69, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_64, B_68))) | ~v1_funct_1(E_69))), inference(resolution, [status(thm)], [c_30, c_207])).
% 3.10/1.62  tff(c_218, plain, (![A_70, B_71, E_72]: (k1_partfun1(A_70, B_71, '#skF_2', '#skF_3', E_72, '#skF_5')=k5_relat_1(E_72, '#skF_5') | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_1(E_72))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_209])).
% 3.10/1.62  tff(c_224, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_218])).
% 3.10/1.62  tff(c_230, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_224])).
% 3.10/1.62  tff(c_255, plain, (![B_78, D_77, F_79, E_80, A_81, C_76]: (m1_subset_1(k1_partfun1(A_81, B_78, C_76, D_77, E_80, F_79), k1_zfmisc_1(k2_zfmisc_1(A_81, D_77))) | ~m1_subset_1(F_79, k1_zfmisc_1(k2_zfmisc_1(C_76, D_77))) | ~v1_funct_1(F_79) | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_78))) | ~v1_funct_1(E_80))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.10/1.62  tff(c_286, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_230, c_255])).
% 3.10/1.62  tff(c_301, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_30, c_286])).
% 3.10/1.62  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.10/1.62  tff(c_350, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_301, c_14])).
% 3.10/1.62  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.10/1.62  tff(c_237, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_22])).
% 3.10/1.62  tff(c_720, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_237])).
% 3.10/1.62  tff(c_761, plain, (k2_relat_1('#skF_5')!='#skF_3' | ~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_133, c_720])).
% 3.10/1.62  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_80, c_90, c_761])).
% 3.10/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.62  
% 3.10/1.62  Inference rules
% 3.10/1.62  ----------------------
% 3.10/1.62  #Ref     : 0
% 3.10/1.62  #Sup     : 157
% 3.10/1.62  #Fact    : 0
% 3.10/1.62  #Define  : 0
% 3.10/1.62  #Split   : 0
% 3.10/1.62  #Chain   : 0
% 3.10/1.62  #Close   : 0
% 3.10/1.62  
% 3.10/1.62  Ordering : KBO
% 3.10/1.62  
% 3.10/1.62  Simplification rules
% 3.10/1.62  ----------------------
% 3.10/1.62  #Subsume      : 2
% 3.10/1.62  #Demod        : 111
% 3.10/1.62  #Tautology    : 33
% 3.10/1.62  #SimpNegUnit  : 0
% 3.10/1.62  #BackRed      : 6
% 3.10/1.62  
% 3.10/1.62  #Partial instantiations: 0
% 3.10/1.62  #Strategies tried      : 1
% 3.10/1.62  
% 3.10/1.62  Timing (in seconds)
% 3.10/1.62  ----------------------
% 3.10/1.62  Preprocessing        : 0.34
% 3.10/1.62  Parsing              : 0.18
% 3.10/1.62  CNF conversion       : 0.02
% 3.10/1.62  Main loop            : 0.39
% 3.10/1.62  Inferencing          : 0.14
% 3.10/1.62  Reduction            : 0.13
% 3.10/1.62  Demodulation         : 0.09
% 3.10/1.62  BG Simplification    : 0.02
% 3.10/1.62  Subsumption          : 0.07
% 3.10/1.62  Abstraction          : 0.02
% 3.10/1.62  MUC search           : 0.00
% 3.10/1.62  Cooper               : 0.00
% 3.10/1.62  Total                : 0.77
% 3.10/1.62  Index Insertion      : 0.00
% 3.10/1.62  Index Deletion       : 0.00
% 3.10/1.62  Index Matching       : 0.00
% 3.10/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
