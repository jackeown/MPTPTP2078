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
% DateTime   : Thu Dec  3 10:11:42 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 375 expanded)
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

tff(f_100,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_49,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_26,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_124,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_132,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_127])).

tff(c_77,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_6])).

tff(c_91,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_105,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_101])).

tff(c_135,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_105])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_130,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_134,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_130])).

tff(c_153,plain,(
    ! [B_46,A_47] :
      ( k9_relat_1(B_46,k2_relat_1(A_47)) = k2_relat_1(k5_relat_1(A_47,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_162,plain,(
    ! [B_46] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_46)) = k9_relat_1(B_46,'#skF_2')
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_153])).

tff(c_172,plain,(
    ! [B_46] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_46)) = k9_relat_1(B_46,'#skF_2')
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_162])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_282,plain,(
    ! [A_74,F_70,D_73,B_72,C_69,E_71] :
      ( k1_partfun1(A_74,B_72,C_69,D_73,E_71,F_70) = k5_relat_1(E_71,F_70)
      | ~ m1_subset_1(F_70,k1_zfmisc_1(k2_zfmisc_1(C_69,D_73)))
      | ~ v1_funct_1(F_70)
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_74,B_72)))
      | ~ v1_funct_1(E_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_284,plain,(
    ! [A_74,B_72,E_71] :
      ( k1_partfun1(A_74,B_72,'#skF_2','#skF_3',E_71,'#skF_5') = k5_relat_1(E_71,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(A_74,B_72)))
      | ~ v1_funct_1(E_71) ) ),
    inference(resolution,[status(thm)],[c_30,c_282])).

tff(c_293,plain,(
    ! [A_75,B_76,E_77] :
      ( k1_partfun1(A_75,B_76,'#skF_2','#skF_3',E_77,'#skF_5') = k5_relat_1(E_77,'#skF_5')
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_1(E_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_284])).

tff(c_299,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_293])).

tff(c_305,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_299])).

tff(c_16,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] :
      ( m1_subset_1(k1_partfun1(A_17,B_18,C_19,D_20,E_21,F_22),k1_zfmisc_1(k2_zfmisc_1(A_17,D_20)))
      | ~ m1_subset_1(F_22,k1_zfmisc_1(k2_zfmisc_1(C_19,D_20)))
      | ~ v1_funct_1(F_22)
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_1(E_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_400,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_16])).

tff(c_404,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_30,c_400])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_481,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_404,c_14])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_396,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_22])).

tff(c_959,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_396])).

tff(c_1000,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_959])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_135,c_1000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:06:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.18/1.53  
% 3.18/1.53  %Foreground sorts:
% 3.18/1.53  
% 3.18/1.53  
% 3.18/1.53  %Background operators:
% 3.18/1.53  
% 3.18/1.53  
% 3.18/1.53  %Foreground operators:
% 3.18/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.18/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.18/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.18/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.18/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.18/1.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.18/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.18/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.18/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.18/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.53  
% 3.42/1.55  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.42/1.55  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.42/1.55  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.42/1.55  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.55  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.42/1.55  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.42/1.55  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.42/1.55  tff(f_78, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.42/1.55  tff(f_68, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.42/1.55  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.55  tff(c_49, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.55  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_49])).
% 3.42/1.55  tff(c_26, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.55  tff(c_124, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.42/1.55  tff(c_127, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_124])).
% 3.42/1.55  tff(c_132, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_127])).
% 3.42/1.55  tff(c_77, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.42/1.55  tff(c_84, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_77])).
% 3.42/1.55  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.55  tff(c_88, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_6])).
% 3.42/1.55  tff(c_91, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88])).
% 3.42/1.55  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.55  tff(c_101, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 3.42/1.55  tff(c_105, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_101])).
% 3.42/1.55  tff(c_135, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_105])).
% 3.42/1.55  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.55  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_49])).
% 3.42/1.55  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.55  tff(c_130, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_124])).
% 3.42/1.55  tff(c_134, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_130])).
% 3.42/1.55  tff(c_153, plain, (![B_46, A_47]: (k9_relat_1(B_46, k2_relat_1(A_47))=k2_relat_1(k5_relat_1(A_47, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.42/1.55  tff(c_162, plain, (![B_46]: (k2_relat_1(k5_relat_1('#skF_4', B_46))=k9_relat_1(B_46, '#skF_2') | ~v1_relat_1(B_46) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_153])).
% 3.42/1.55  tff(c_172, plain, (![B_46]: (k2_relat_1(k5_relat_1('#skF_4', B_46))=k9_relat_1(B_46, '#skF_2') | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_162])).
% 3.42/1.55  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.55  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.55  tff(c_282, plain, (![A_74, F_70, D_73, B_72, C_69, E_71]: (k1_partfun1(A_74, B_72, C_69, D_73, E_71, F_70)=k5_relat_1(E_71, F_70) | ~m1_subset_1(F_70, k1_zfmisc_1(k2_zfmisc_1(C_69, D_73))) | ~v1_funct_1(F_70) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_74, B_72))) | ~v1_funct_1(E_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.42/1.55  tff(c_284, plain, (![A_74, B_72, E_71]: (k1_partfun1(A_74, B_72, '#skF_2', '#skF_3', E_71, '#skF_5')=k5_relat_1(E_71, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(A_74, B_72))) | ~v1_funct_1(E_71))), inference(resolution, [status(thm)], [c_30, c_282])).
% 3.42/1.55  tff(c_293, plain, (![A_75, B_76, E_77]: (k1_partfun1(A_75, B_76, '#skF_2', '#skF_3', E_77, '#skF_5')=k5_relat_1(E_77, '#skF_5') | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_1(E_77))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_284])).
% 3.42/1.55  tff(c_299, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_293])).
% 3.42/1.55  tff(c_305, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_299])).
% 3.42/1.55  tff(c_16, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (m1_subset_1(k1_partfun1(A_17, B_18, C_19, D_20, E_21, F_22), k1_zfmisc_1(k2_zfmisc_1(A_17, D_20))) | ~m1_subset_1(F_22, k1_zfmisc_1(k2_zfmisc_1(C_19, D_20))) | ~v1_funct_1(F_22) | ~m1_subset_1(E_21, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_1(E_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.55  tff(c_400, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_305, c_16])).
% 3.42/1.55  tff(c_404, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_30, c_400])).
% 3.42/1.55  tff(c_14, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.42/1.55  tff(c_481, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_404, c_14])).
% 3.42/1.55  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.55  tff(c_396, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_22])).
% 3.42/1.55  tff(c_959, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_396])).
% 3.42/1.55  tff(c_1000, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_172, c_959])).
% 3.42/1.55  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_135, c_1000])).
% 3.42/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  Inference rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Ref     : 0
% 3.42/1.55  #Sup     : 223
% 3.42/1.55  #Fact    : 0
% 3.42/1.55  #Define  : 0
% 3.42/1.55  #Split   : 0
% 3.42/1.55  #Chain   : 0
% 3.42/1.55  #Close   : 0
% 3.42/1.55  
% 3.42/1.55  Ordering : KBO
% 3.42/1.55  
% 3.42/1.55  Simplification rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Subsume      : 2
% 3.42/1.55  #Demod        : 158
% 3.42/1.55  #Tautology    : 72
% 3.42/1.55  #SimpNegUnit  : 0
% 3.42/1.55  #BackRed      : 8
% 3.42/1.55  
% 3.42/1.55  #Partial instantiations: 0
% 3.42/1.55  #Strategies tried      : 1
% 3.42/1.55  
% 3.42/1.55  Timing (in seconds)
% 3.42/1.55  ----------------------
% 3.42/1.55  Preprocessing        : 0.32
% 3.42/1.55  Parsing              : 0.18
% 3.42/1.55  CNF conversion       : 0.02
% 3.42/1.55  Main loop            : 0.45
% 3.42/1.55  Inferencing          : 0.17
% 3.42/1.55  Reduction            : 0.15
% 3.42/1.55  Demodulation         : 0.11
% 3.42/1.55  BG Simplification    : 0.02
% 3.42/1.55  Subsumption          : 0.08
% 3.42/1.55  Abstraction          : 0.02
% 3.42/1.55  MUC search           : 0.00
% 3.42/1.55  Cooper               : 0.00
% 3.42/1.55  Total                : 0.81
% 3.42/1.55  Index Insertion      : 0.00
% 3.42/1.55  Index Deletion       : 0.00
% 3.42/1.55  Index Matching       : 0.00
% 3.42/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
