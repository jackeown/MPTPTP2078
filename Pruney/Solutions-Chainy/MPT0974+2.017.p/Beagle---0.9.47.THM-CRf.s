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
% DateTime   : Thu Dec  3 10:11:43 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 138 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 399 expanded)
%              Number of equality atoms :   37 ( 130 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_105,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_28,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_143,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_149,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_143])).

tff(c_153,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_149])).

tff(c_84,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_10])).

tff(c_104,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_101])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6])).

tff(c_121,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_117])).

tff(c_164,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_121])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_55,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_55])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_146,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_143])).

tff(c_151,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_146])).

tff(c_8,plain,(
    ! [B_10,A_8] :
      ( k9_relat_1(B_10,k2_relat_1(A_8)) = k2_relat_1(k5_relat_1(A_8,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_158,plain,(
    ! [B_10] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_10)) = k9_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_8])).

tff(c_162,plain,(
    ! [B_10] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_10)) = k9_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_158])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_289,plain,(
    ! [F_75,E_77,C_74,D_72,A_73,B_76] :
      ( k1_partfun1(A_73,B_76,C_74,D_72,E_77,F_75) = k5_relat_1(E_77,F_75)
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(C_74,D_72)))
      | ~ v1_funct_1(F_75)
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_73,B_76)))
      | ~ v1_funct_1(E_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_293,plain,(
    ! [A_73,B_76,E_77] :
      ( k1_partfun1(A_73,B_76,'#skF_2','#skF_3',E_77,'#skF_5') = k5_relat_1(E_77,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_73,B_76)))
      | ~ v1_funct_1(E_77) ) ),
    inference(resolution,[status(thm)],[c_32,c_289])).

tff(c_422,plain,(
    ! [A_87,B_88,E_89] :
      ( k1_partfun1(A_87,B_88,'#skF_2','#skF_3',E_89,'#skF_5') = k5_relat_1(E_89,'#skF_5')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_293])).

tff(c_431,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_422])).

tff(c_441,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_431])).

tff(c_18,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( m1_subset_1(k1_partfun1(A_19,B_20,C_21,D_22,E_23,F_24),k1_zfmisc_1(k2_zfmisc_1(A_19,D_22)))
      | ~ m1_subset_1(F_24,k1_zfmisc_1(k2_zfmisc_1(C_21,D_22)))
      | ~ v1_funct_1(F_24)
      | ~ m1_subset_1(E_23,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_1(E_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_508,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_18])).

tff(c_512,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_32,c_508])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_560,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_512,c_16])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_504,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_24])).

tff(c_972,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_504])).

tff(c_1013,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_972])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_164,c_1013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.34/1.52  
% 3.34/1.52  %Foreground sorts:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Background operators:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Foreground operators:
% 3.34/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.34/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.34/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.34/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.34/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.34/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.34/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.52  
% 3.34/1.53  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.34/1.53  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.34/1.53  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.34/1.53  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.34/1.53  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.34/1.53  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.34/1.53  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.34/1.53  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.34/1.53  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.34/1.53  tff(f_73, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.34/1.53  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.34/1.53  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.53  tff(c_52, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.53  tff(c_58, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_52])).
% 3.34/1.53  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_58])).
% 3.34/1.53  tff(c_28, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.53  tff(c_143, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.34/1.53  tff(c_149, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_143])).
% 3.34/1.53  tff(c_153, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_149])).
% 3.34/1.53  tff(c_84, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.34/1.53  tff(c_92, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_84])).
% 3.34/1.53  tff(c_10, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.34/1.53  tff(c_101, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_10])).
% 3.34/1.53  tff(c_104, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_101])).
% 3.34/1.53  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.53  tff(c_117, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_104, c_6])).
% 3.34/1.53  tff(c_121, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_117])).
% 3.34/1.53  tff(c_164, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_121])).
% 3.34/1.53  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.53  tff(c_55, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_52])).
% 3.34/1.53  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_55])).
% 3.34/1.53  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.53  tff(c_146, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_143])).
% 3.34/1.53  tff(c_151, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_146])).
% 3.34/1.53  tff(c_8, plain, (![B_10, A_8]: (k9_relat_1(B_10, k2_relat_1(A_8))=k2_relat_1(k5_relat_1(A_8, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.53  tff(c_158, plain, (![B_10]: (k2_relat_1(k5_relat_1('#skF_4', B_10))=k9_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_8])).
% 3.34/1.53  tff(c_162, plain, (![B_10]: (k2_relat_1(k5_relat_1('#skF_4', B_10))=k9_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_158])).
% 3.34/1.53  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.53  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.53  tff(c_289, plain, (![F_75, E_77, C_74, D_72, A_73, B_76]: (k1_partfun1(A_73, B_76, C_74, D_72, E_77, F_75)=k5_relat_1(E_77, F_75) | ~m1_subset_1(F_75, k1_zfmisc_1(k2_zfmisc_1(C_74, D_72))) | ~v1_funct_1(F_75) | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_73, B_76))) | ~v1_funct_1(E_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.34/1.53  tff(c_293, plain, (![A_73, B_76, E_77]: (k1_partfun1(A_73, B_76, '#skF_2', '#skF_3', E_77, '#skF_5')=k5_relat_1(E_77, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_73, B_76))) | ~v1_funct_1(E_77))), inference(resolution, [status(thm)], [c_32, c_289])).
% 3.34/1.53  tff(c_422, plain, (![A_87, B_88, E_89]: (k1_partfun1(A_87, B_88, '#skF_2', '#skF_3', E_89, '#skF_5')=k5_relat_1(E_89, '#skF_5') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_1(E_89))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_293])).
% 3.34/1.53  tff(c_431, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_422])).
% 3.34/1.53  tff(c_441, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_431])).
% 3.34/1.53  tff(c_18, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (m1_subset_1(k1_partfun1(A_19, B_20, C_21, D_22, E_23, F_24), k1_zfmisc_1(k2_zfmisc_1(A_19, D_22))) | ~m1_subset_1(F_24, k1_zfmisc_1(k2_zfmisc_1(C_21, D_22))) | ~v1_funct_1(F_24) | ~m1_subset_1(E_23, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_1(E_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.34/1.53  tff(c_508, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_441, c_18])).
% 3.34/1.53  tff(c_512, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_32, c_508])).
% 3.34/1.53  tff(c_16, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.34/1.53  tff(c_560, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_512, c_16])).
% 3.34/1.53  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.53  tff(c_504, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_24])).
% 3.34/1.53  tff(c_972, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_504])).
% 3.34/1.53  tff(c_1013, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_162, c_972])).
% 3.34/1.53  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_164, c_1013])).
% 3.34/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.53  
% 3.34/1.53  Inference rules
% 3.34/1.53  ----------------------
% 3.34/1.53  #Ref     : 0
% 3.34/1.53  #Sup     : 221
% 3.34/1.53  #Fact    : 0
% 3.34/1.53  #Define  : 0
% 3.34/1.53  #Split   : 0
% 3.34/1.53  #Chain   : 0
% 3.34/1.53  #Close   : 0
% 3.34/1.53  
% 3.34/1.53  Ordering : KBO
% 3.34/1.53  
% 3.34/1.53  Simplification rules
% 3.34/1.53  ----------------------
% 3.34/1.53  #Subsume      : 2
% 3.34/1.53  #Demod        : 165
% 3.34/1.53  #Tautology    : 70
% 3.34/1.53  #SimpNegUnit  : 0
% 3.34/1.53  #BackRed      : 8
% 3.34/1.53  
% 3.34/1.53  #Partial instantiations: 0
% 3.34/1.53  #Strategies tried      : 1
% 3.34/1.53  
% 3.34/1.53  Timing (in seconds)
% 3.34/1.53  ----------------------
% 3.55/1.54  Preprocessing        : 0.32
% 3.55/1.54  Parsing              : 0.17
% 3.55/1.54  CNF conversion       : 0.02
% 3.55/1.54  Main loop            : 0.45
% 3.55/1.54  Inferencing          : 0.17
% 3.55/1.54  Reduction            : 0.15
% 3.55/1.54  Demodulation         : 0.11
% 3.55/1.54  BG Simplification    : 0.02
% 3.55/1.54  Subsumption          : 0.07
% 3.55/1.54  Abstraction          : 0.02
% 3.55/1.54  MUC search           : 0.00
% 3.55/1.54  Cooper               : 0.00
% 3.55/1.54  Total                : 0.80
% 3.55/1.54  Index Insertion      : 0.00
% 3.55/1.54  Index Deletion       : 0.00
% 3.55/1.54  Index Matching       : 0.00
% 3.55/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
