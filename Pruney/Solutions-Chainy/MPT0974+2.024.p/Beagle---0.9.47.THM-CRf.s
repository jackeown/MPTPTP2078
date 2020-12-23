%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:44 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 113 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 338 expanded)
%              Number of equality atoms :   34 ( 117 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_99,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_125,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k7_relset_1(A_43,B_44,C_45,D_46) = k9_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    ! [D_46] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_46) = k9_relat_1('#skF_5',D_46) ),
    inference(resolution,[status(thm)],[c_30,c_125])).

tff(c_26,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_150,plain,(
    ! [A_49,B_50,C_51] :
      ( k7_relset_1(A_49,B_50,C_51,A_49) = k2_relset_1(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_2') = k2_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_158,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_26,c_154])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_59,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_relset_1(A_36,B_37,C_38) = k2_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_71,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_66])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( k9_relat_1(B_8,k2_relat_1(A_6)) = k2_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [B_8] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_8)) = k9_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_6])).

tff(c_90,plain,(
    ! [B_8] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_8)) = k9_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_86])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_230,plain,(
    ! [C_70,E_73,F_71,B_72,D_68,A_69] :
      ( k1_partfun1(A_69,B_72,C_70,D_68,E_73,F_71) = k5_relat_1(E_73,F_71)
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(C_70,D_68)))
      | ~ v1_funct_1(F_71)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_69,B_72)))
      | ~ v1_funct_1(E_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_234,plain,(
    ! [A_69,B_72,E_73] :
      ( k1_partfun1(A_69,B_72,'#skF_2','#skF_3',E_73,'#skF_5') = k5_relat_1(E_73,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_69,B_72)))
      | ~ v1_funct_1(E_73) ) ),
    inference(resolution,[status(thm)],[c_30,c_230])).

tff(c_254,plain,(
    ! [A_77,B_78,E_79] :
      ( k1_partfun1(A_77,B_78,'#skF_2','#skF_3',E_79,'#skF_5') = k5_relat_1(E_79,'#skF_5')
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(E_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_234])).

tff(c_257,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_254])).

tff(c_263,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_257])).

tff(c_278,plain,(
    ! [F_84,D_85,C_80,B_82,A_83,E_81] :
      ( m1_subset_1(k1_partfun1(A_83,B_82,C_80,D_85,E_81,F_84),k1_zfmisc_1(k2_zfmisc_1(A_83,D_85)))
      | ~ m1_subset_1(F_84,k1_zfmisc_1(k2_zfmisc_1(C_80,D_85)))
      | ~ v1_funct_1(F_84)
      | ~ m1_subset_1(E_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_1(E_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_309,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_278])).

tff(c_325,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_30,c_309])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_416,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_325,c_8])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_268,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_22])).

tff(c_725,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_268])).

tff(c_732,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_725])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_158,c_732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.20/1.51  
% 3.20/1.51  %Foreground sorts:
% 3.20/1.51  
% 3.20/1.51  
% 3.20/1.51  %Background operators:
% 3.20/1.51  
% 3.20/1.51  
% 3.20/1.51  %Foreground operators:
% 3.20/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.20/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.20/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.20/1.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.51  
% 3.20/1.52  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.20/1.52  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 3.20/1.52  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.20/1.52  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.20/1.52  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.20/1.52  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.20/1.52  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.20/1.52  tff(f_77, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.20/1.52  tff(f_67, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.20/1.52  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.20/1.52  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.52  tff(c_50, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.52  tff(c_56, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_50])).
% 3.20/1.52  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_56])).
% 3.20/1.52  tff(c_125, plain, (![A_43, B_44, C_45, D_46]: (k7_relset_1(A_43, B_44, C_45, D_46)=k9_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.52  tff(c_131, plain, (![D_46]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_46)=k9_relat_1('#skF_5', D_46))), inference(resolution, [status(thm)], [c_30, c_125])).
% 3.20/1.52  tff(c_26, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.52  tff(c_150, plain, (![A_49, B_50, C_51]: (k7_relset_1(A_49, B_50, C_51, A_49)=k2_relset_1(A_49, B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.52  tff(c_154, plain, (k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_2')=k2_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_150])).
% 3.20/1.52  tff(c_158, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_26, c_154])).
% 3.20/1.52  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.52  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_50])).
% 3.20/1.52  tff(c_59, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_53])).
% 3.20/1.52  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.52  tff(c_63, plain, (![A_36, B_37, C_38]: (k2_relset_1(A_36, B_37, C_38)=k2_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.52  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_63])).
% 3.20/1.52  tff(c_71, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_66])).
% 3.20/1.52  tff(c_6, plain, (![B_8, A_6]: (k9_relat_1(B_8, k2_relat_1(A_6))=k2_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.52  tff(c_86, plain, (![B_8]: (k2_relat_1(k5_relat_1('#skF_4', B_8))=k9_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_6])).
% 3.20/1.52  tff(c_90, plain, (![B_8]: (k2_relat_1(k5_relat_1('#skF_4', B_8))=k9_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_86])).
% 3.20/1.52  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.52  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.52  tff(c_230, plain, (![C_70, E_73, F_71, B_72, D_68, A_69]: (k1_partfun1(A_69, B_72, C_70, D_68, E_73, F_71)=k5_relat_1(E_73, F_71) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(C_70, D_68))) | ~v1_funct_1(F_71) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_69, B_72))) | ~v1_funct_1(E_73))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.52  tff(c_234, plain, (![A_69, B_72, E_73]: (k1_partfun1(A_69, B_72, '#skF_2', '#skF_3', E_73, '#skF_5')=k5_relat_1(E_73, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_69, B_72))) | ~v1_funct_1(E_73))), inference(resolution, [status(thm)], [c_30, c_230])).
% 3.20/1.52  tff(c_254, plain, (![A_77, B_78, E_79]: (k1_partfun1(A_77, B_78, '#skF_2', '#skF_3', E_79, '#skF_5')=k5_relat_1(E_79, '#skF_5') | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(E_79))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_234])).
% 3.20/1.52  tff(c_257, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_254])).
% 3.20/1.52  tff(c_263, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_257])).
% 3.20/1.52  tff(c_278, plain, (![F_84, D_85, C_80, B_82, A_83, E_81]: (m1_subset_1(k1_partfun1(A_83, B_82, C_80, D_85, E_81, F_84), k1_zfmisc_1(k2_zfmisc_1(A_83, D_85))) | ~m1_subset_1(F_84, k1_zfmisc_1(k2_zfmisc_1(C_80, D_85))) | ~v1_funct_1(F_84) | ~m1_subset_1(E_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_1(E_81))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.52  tff(c_309, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_263, c_278])).
% 3.20/1.52  tff(c_325, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_30, c_309])).
% 3.20/1.52  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.52  tff(c_416, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_325, c_8])).
% 3.20/1.52  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.52  tff(c_268, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_22])).
% 3.20/1.52  tff(c_725, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_416, c_268])).
% 3.20/1.52  tff(c_732, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_725])).
% 3.20/1.52  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_158, c_732])).
% 3.20/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  Inference rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Ref     : 0
% 3.20/1.52  #Sup     : 156
% 3.20/1.52  #Fact    : 0
% 3.20/1.52  #Define  : 0
% 3.20/1.52  #Split   : 0
% 3.20/1.52  #Chain   : 0
% 3.20/1.52  #Close   : 0
% 3.20/1.52  
% 3.20/1.52  Ordering : KBO
% 3.20/1.52  
% 3.20/1.52  Simplification rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Subsume      : 0
% 3.20/1.52  #Demod        : 107
% 3.20/1.52  #Tautology    : 44
% 3.20/1.52  #SimpNegUnit  : 0
% 3.20/1.52  #BackRed      : 6
% 3.20/1.52  
% 3.20/1.52  #Partial instantiations: 0
% 3.20/1.52  #Strategies tried      : 1
% 3.20/1.52  
% 3.20/1.52  Timing (in seconds)
% 3.20/1.52  ----------------------
% 3.20/1.52  Preprocessing        : 0.32
% 3.20/1.52  Parsing              : 0.18
% 3.20/1.52  CNF conversion       : 0.02
% 3.20/1.52  Main loop            : 0.38
% 3.20/1.53  Inferencing          : 0.15
% 3.20/1.53  Reduction            : 0.12
% 3.20/1.53  Demodulation         : 0.09
% 3.20/1.53  BG Simplification    : 0.02
% 3.20/1.53  Subsumption          : 0.06
% 3.20/1.53  Abstraction          : 0.02
% 3.20/1.53  MUC search           : 0.00
% 3.20/1.53  Cooper               : 0.00
% 3.20/1.53  Total                : 0.74
% 3.20/1.53  Index Insertion      : 0.00
% 3.20/1.53  Index Deletion       : 0.00
% 3.20/1.53  Index Matching       : 0.00
% 3.20/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
