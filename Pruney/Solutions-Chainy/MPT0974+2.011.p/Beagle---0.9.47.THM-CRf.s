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
% DateTime   : Thu Dec  3 10:11:43 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 126 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 400 expanded)
%              Number of equality atoms :   49 ( 150 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_110,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_34,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_84,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_relset_1(A_36,B_37,C_38) = k2_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_92,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_87])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_138,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_138])).

tff(c_158,plain,(
    ! [B_51,A_52,C_53] :
      ( k1_xboole_0 = B_51
      | k1_relset_1(A_52,B_51,C_53) = A_52
      | ~ v1_funct_2(C_53,A_52,B_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_161,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_167,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_145,c_161])).

tff(c_168,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_167])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_176,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_2])).

tff(c_180,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_92,c_176])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_94,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_90])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( k9_relat_1(B_4,k2_relat_1(A_2)) = k2_relat_1(k5_relat_1(A_2,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_107,plain,(
    ! [B_4] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_4)) = k9_relat_1(B_4,'#skF_2')
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4])).

tff(c_111,plain,(
    ! [B_4] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_4)) = k9_relat_1(B_4,'#skF_2')
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_107])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_284,plain,(
    ! [F_74,D_77,C_73,A_78,E_75,B_76] :
      ( k1_partfun1(A_78,B_76,C_73,D_77,E_75,F_74) = k5_relat_1(E_75,F_74)
      | ~ m1_subset_1(F_74,k1_zfmisc_1(k2_zfmisc_1(C_73,D_77)))
      | ~ v1_funct_1(F_74)
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_78,B_76)))
      | ~ v1_funct_1(E_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_286,plain,(
    ! [A_78,B_76,E_75] :
      ( k1_partfun1(A_78,B_76,'#skF_2','#skF_3',E_75,'#skF_5') = k5_relat_1(E_75,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_78,B_76)))
      | ~ v1_funct_1(E_75) ) ),
    inference(resolution,[status(thm)],[c_38,c_284])).

tff(c_295,plain,(
    ! [A_79,B_80,E_81] :
      ( k1_partfun1(A_79,B_80,'#skF_2','#skF_3',E_81,'#skF_5') = k5_relat_1(E_81,'#skF_5')
      | ~ m1_subset_1(E_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(E_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_286])).

tff(c_301,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_295])).

tff(c_307,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_301])).

tff(c_337,plain,(
    ! [C_85,E_90,B_87,D_89,F_88,A_86] :
      ( m1_subset_1(k1_partfun1(A_86,B_87,C_85,D_89,E_90,F_88),k1_zfmisc_1(k2_zfmisc_1(A_86,D_89)))
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_85,D_89)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(E_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_386,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_337])).

tff(c_407,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_38,c_386])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_579,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_407,c_10])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_314,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_30])).

tff(c_780,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_314])).

tff(c_787,plain,
    ( k9_relat_1('#skF_5','#skF_2') != '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_780])).

tff(c_790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_180,c_787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:39:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.52  
% 3.04/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.52  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.04/1.52  
% 3.04/1.52  %Foreground sorts:
% 3.04/1.52  
% 3.04/1.52  
% 3.04/1.52  %Background operators:
% 3.04/1.52  
% 3.04/1.52  
% 3.04/1.52  %Foreground operators:
% 3.04/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.04/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.04/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.04/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.04/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.04/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.52  
% 3.13/1.54  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.13/1.54  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.13/1.54  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.13/1.54  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.13/1.54  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.13/1.54  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.13/1.54  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.13/1.54  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.13/1.54  tff(f_78, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.13/1.54  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_66, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.13/1.54  tff(c_73, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_66])).
% 3.13/1.54  tff(c_34, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_84, plain, (![A_36, B_37, C_38]: (k2_relset_1(A_36, B_37, C_38)=k2_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.13/1.54  tff(c_87, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_84])).
% 3.13/1.54  tff(c_92, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_87])).
% 3.13/1.54  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_138, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.54  tff(c_145, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_138])).
% 3.13/1.54  tff(c_158, plain, (![B_51, A_52, C_53]: (k1_xboole_0=B_51 | k1_relset_1(A_52, B_51, C_53)=A_52 | ~v1_funct_2(C_53, A_52, B_51) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.54  tff(c_161, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_158])).
% 3.13/1.54  tff(c_167, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_145, c_161])).
% 3.13/1.54  tff(c_168, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_167])).
% 3.13/1.54  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.54  tff(c_176, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_168, c_2])).
% 3.13/1.54  tff(c_180, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_92, c_176])).
% 3.13/1.54  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.13/1.54  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_84])).
% 3.13/1.54  tff(c_94, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_90])).
% 3.13/1.54  tff(c_4, plain, (![B_4, A_2]: (k9_relat_1(B_4, k2_relat_1(A_2))=k2_relat_1(k5_relat_1(A_2, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.13/1.54  tff(c_107, plain, (![B_4]: (k2_relat_1(k5_relat_1('#skF_4', B_4))=k9_relat_1(B_4, '#skF_2') | ~v1_relat_1(B_4) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_4])).
% 3.13/1.54  tff(c_111, plain, (![B_4]: (k2_relat_1(k5_relat_1('#skF_4', B_4))=k9_relat_1(B_4, '#skF_2') | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_107])).
% 3.13/1.54  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_284, plain, (![F_74, D_77, C_73, A_78, E_75, B_76]: (k1_partfun1(A_78, B_76, C_73, D_77, E_75, F_74)=k5_relat_1(E_75, F_74) | ~m1_subset_1(F_74, k1_zfmisc_1(k2_zfmisc_1(C_73, D_77))) | ~v1_funct_1(F_74) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_78, B_76))) | ~v1_funct_1(E_75))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.13/1.54  tff(c_286, plain, (![A_78, B_76, E_75]: (k1_partfun1(A_78, B_76, '#skF_2', '#skF_3', E_75, '#skF_5')=k5_relat_1(E_75, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_78, B_76))) | ~v1_funct_1(E_75))), inference(resolution, [status(thm)], [c_38, c_284])).
% 3.13/1.54  tff(c_295, plain, (![A_79, B_80, E_81]: (k1_partfun1(A_79, B_80, '#skF_2', '#skF_3', E_81, '#skF_5')=k5_relat_1(E_81, '#skF_5') | ~m1_subset_1(E_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(E_81))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_286])).
% 3.13/1.54  tff(c_301, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_295])).
% 3.13/1.54  tff(c_307, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_301])).
% 3.13/1.54  tff(c_337, plain, (![C_85, E_90, B_87, D_89, F_88, A_86]: (m1_subset_1(k1_partfun1(A_86, B_87, C_85, D_89, E_90, F_88), k1_zfmisc_1(k2_zfmisc_1(A_86, D_89))) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_85, D_89))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(E_90))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.13/1.54  tff(c_386, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_307, c_337])).
% 3.13/1.54  tff(c_407, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_38, c_386])).
% 3.13/1.54  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.13/1.54  tff(c_579, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_407, c_10])).
% 3.13/1.54  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.54  tff(c_314, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_30])).
% 3.13/1.54  tff(c_780, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_314])).
% 3.13/1.54  tff(c_787, plain, (k9_relat_1('#skF_5', '#skF_2')!='#skF_3' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_111, c_780])).
% 3.13/1.54  tff(c_790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_180, c_787])).
% 3.13/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.54  
% 3.13/1.54  Inference rules
% 3.13/1.54  ----------------------
% 3.13/1.54  #Ref     : 0
% 3.13/1.54  #Sup     : 174
% 3.13/1.54  #Fact    : 0
% 3.13/1.54  #Define  : 0
% 3.13/1.54  #Split   : 3
% 3.13/1.54  #Chain   : 0
% 3.13/1.54  #Close   : 0
% 3.13/1.54  
% 3.13/1.54  Ordering : KBO
% 3.13/1.54  
% 3.13/1.54  Simplification rules
% 3.13/1.54  ----------------------
% 3.13/1.54  #Subsume      : 0
% 3.13/1.54  #Demod        : 98
% 3.13/1.54  #Tautology    : 62
% 3.13/1.54  #SimpNegUnit  : 8
% 3.13/1.54  #BackRed      : 10
% 3.13/1.54  
% 3.13/1.54  #Partial instantiations: 0
% 3.13/1.54  #Strategies tried      : 1
% 3.13/1.54  
% 3.13/1.54  Timing (in seconds)
% 3.13/1.54  ----------------------
% 3.13/1.54  Preprocessing        : 0.34
% 3.13/1.54  Parsing              : 0.18
% 3.13/1.54  CNF conversion       : 0.02
% 3.13/1.54  Main loop            : 0.37
% 3.13/1.54  Inferencing          : 0.14
% 3.13/1.54  Reduction            : 0.12
% 3.13/1.54  Demodulation         : 0.08
% 3.13/1.54  BG Simplification    : 0.02
% 3.13/1.54  Subsumption          : 0.06
% 3.13/1.54  Abstraction          : 0.02
% 3.13/1.54  MUC search           : 0.00
% 3.13/1.54  Cooper               : 0.00
% 3.13/1.54  Total                : 0.74
% 3.13/1.54  Index Insertion      : 0.00
% 3.13/1.54  Index Deletion       : 0.00
% 3.13/1.54  Index Matching       : 0.00
% 3.13/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
