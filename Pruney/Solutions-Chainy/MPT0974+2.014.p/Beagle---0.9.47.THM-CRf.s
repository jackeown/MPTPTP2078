%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:43 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 116 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 352 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_80,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_80])).

tff(c_28,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_89,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_relset_1(A_44,B_45,C_46) = k2_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_89])).

tff(c_99,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_95])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_55,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_92,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_97,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_92])).

tff(c_108,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(k5_relat_1(B_47,A_48)) = k2_relat_1(A_48)
      | ~ r1_tarski(k1_relat_1(A_48),k2_relat_1(B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_114,plain,(
    ! [A_48] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_48)) = k2_relat_1(A_48)
      | ~ r1_tarski(k1_relat_1(A_48),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_108])).

tff(c_142,plain,(
    ! [A_51] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_51)) = k2_relat_1(A_51)
      | ~ r1_tarski(k1_relat_1(A_51),'#skF_2')
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_114])).

tff(c_147,plain,(
    ! [B_5] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_5)) = k2_relat_1(B_5)
      | ~ v4_relat_1(B_5,'#skF_2')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_231,plain,(
    ! [C_68,E_70,D_72,A_73,B_71,F_69] :
      ( k1_partfun1(A_73,B_71,C_68,D_72,E_70,F_69) = k5_relat_1(E_70,F_69)
      | ~ m1_subset_1(F_69,k1_zfmisc_1(k2_zfmisc_1(C_68,D_72)))
      | ~ v1_funct_1(F_69)
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_73,B_71)))
      | ~ v1_funct_1(E_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_235,plain,(
    ! [A_73,B_71,E_70] :
      ( k1_partfun1(A_73,B_71,'#skF_2','#skF_3',E_70,'#skF_5') = k5_relat_1(E_70,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_73,B_71)))
      | ~ v1_funct_1(E_70) ) ),
    inference(resolution,[status(thm)],[c_32,c_231])).

tff(c_255,plain,(
    ! [A_77,B_78,E_79] :
      ( k1_partfun1(A_77,B_78,'#skF_2','#skF_3',E_79,'#skF_5') = k5_relat_1(E_79,'#skF_5')
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(E_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_235])).

tff(c_258,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_255])).

tff(c_264,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_258])).

tff(c_274,plain,(
    ! [C_80,A_81,D_84,B_82,E_85,F_83] :
      ( m1_subset_1(k1_partfun1(A_81,B_82,C_80,D_84,E_85,F_83),k1_zfmisc_1(k2_zfmisc_1(A_81,D_84)))
      | ~ m1_subset_1(F_83,k1_zfmisc_1(k2_zfmisc_1(C_80,D_84)))
      | ~ v1_funct_1(F_83)
      | ~ m1_subset_1(E_85,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_1(E_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_302,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_274])).

tff(c_315,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_32,c_302])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_356,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_315,c_16])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_269,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_24])).

tff(c_650,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_269])).

tff(c_657,plain,
    ( k2_relat_1('#skF_5') != '#skF_3'
    | ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_650])).

tff(c_660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_88,c_99,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.47  
% 2.91/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.47  
% 2.91/1.47  %Foreground sorts:
% 2.91/1.47  
% 2.91/1.47  
% 2.91/1.47  %Background operators:
% 2.91/1.47  
% 2.91/1.47  
% 2.91/1.47  %Foreground operators:
% 2.91/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.91/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.91/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.47  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.47  
% 3.07/1.48  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.07/1.48  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.07/1.48  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.07/1.48  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.07/1.48  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.07/1.48  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.07/1.48  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.07/1.48  tff(f_81, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.07/1.48  tff(f_71, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.07/1.48  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.48  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.48  tff(c_52, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.48  tff(c_58, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_52])).
% 3.07/1.48  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_58])).
% 3.07/1.48  tff(c_80, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.07/1.48  tff(c_88, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_80])).
% 3.07/1.48  tff(c_28, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.48  tff(c_89, plain, (![A_44, B_45, C_46]: (k2_relset_1(A_44, B_45, C_46)=k2_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.07/1.48  tff(c_95, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_89])).
% 3.07/1.48  tff(c_99, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_95])).
% 3.07/1.48  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.07/1.48  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.48  tff(c_55, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_52])).
% 3.07/1.48  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55])).
% 3.07/1.48  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.48  tff(c_92, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_89])).
% 3.07/1.48  tff(c_97, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_92])).
% 3.07/1.48  tff(c_108, plain, (![B_47, A_48]: (k2_relat_1(k5_relat_1(B_47, A_48))=k2_relat_1(A_48) | ~r1_tarski(k1_relat_1(A_48), k2_relat_1(B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.48  tff(c_114, plain, (![A_48]: (k2_relat_1(k5_relat_1('#skF_4', A_48))=k2_relat_1(A_48) | ~r1_tarski(k1_relat_1(A_48), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_97, c_108])).
% 3.07/1.48  tff(c_142, plain, (![A_51]: (k2_relat_1(k5_relat_1('#skF_4', A_51))=k2_relat_1(A_51) | ~r1_tarski(k1_relat_1(A_51), '#skF_2') | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_114])).
% 3.07/1.48  tff(c_147, plain, (![B_5]: (k2_relat_1(k5_relat_1('#skF_4', B_5))=k2_relat_1(B_5) | ~v4_relat_1(B_5, '#skF_2') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_142])).
% 3.07/1.48  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.48  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.48  tff(c_231, plain, (![C_68, E_70, D_72, A_73, B_71, F_69]: (k1_partfun1(A_73, B_71, C_68, D_72, E_70, F_69)=k5_relat_1(E_70, F_69) | ~m1_subset_1(F_69, k1_zfmisc_1(k2_zfmisc_1(C_68, D_72))) | ~v1_funct_1(F_69) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_73, B_71))) | ~v1_funct_1(E_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.07/1.48  tff(c_235, plain, (![A_73, B_71, E_70]: (k1_partfun1(A_73, B_71, '#skF_2', '#skF_3', E_70, '#skF_5')=k5_relat_1(E_70, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_73, B_71))) | ~v1_funct_1(E_70))), inference(resolution, [status(thm)], [c_32, c_231])).
% 3.07/1.48  tff(c_255, plain, (![A_77, B_78, E_79]: (k1_partfun1(A_77, B_78, '#skF_2', '#skF_3', E_79, '#skF_5')=k5_relat_1(E_79, '#skF_5') | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(E_79))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_235])).
% 3.07/1.48  tff(c_258, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_255])).
% 3.07/1.48  tff(c_264, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_258])).
% 3.07/1.48  tff(c_274, plain, (![C_80, A_81, D_84, B_82, E_85, F_83]: (m1_subset_1(k1_partfun1(A_81, B_82, C_80, D_84, E_85, F_83), k1_zfmisc_1(k2_zfmisc_1(A_81, D_84))) | ~m1_subset_1(F_83, k1_zfmisc_1(k2_zfmisc_1(C_80, D_84))) | ~v1_funct_1(F_83) | ~m1_subset_1(E_85, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_1(E_85))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.48  tff(c_302, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_264, c_274])).
% 3.07/1.48  tff(c_315, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_32, c_302])).
% 3.07/1.48  tff(c_16, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.07/1.48  tff(c_356, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_315, c_16])).
% 3.07/1.48  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.48  tff(c_269, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_24])).
% 3.07/1.48  tff(c_650, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_356, c_269])).
% 3.07/1.48  tff(c_657, plain, (k2_relat_1('#skF_5')!='#skF_3' | ~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_147, c_650])).
% 3.07/1.48  tff(c_660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_88, c_99, c_657])).
% 3.07/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  Inference rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Ref     : 0
% 3.07/1.48  #Sup     : 133
% 3.07/1.48  #Fact    : 0
% 3.07/1.48  #Define  : 0
% 3.07/1.48  #Split   : 0
% 3.07/1.48  #Chain   : 0
% 3.07/1.48  #Close   : 0
% 3.07/1.48  
% 3.07/1.48  Ordering : KBO
% 3.07/1.48  
% 3.07/1.48  Simplification rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Subsume      : 2
% 3.07/1.48  #Demod        : 90
% 3.07/1.48  #Tautology    : 31
% 3.07/1.48  #SimpNegUnit  : 0
% 3.07/1.48  #BackRed      : 6
% 3.07/1.48  
% 3.07/1.48  #Partial instantiations: 0
% 3.07/1.48  #Strategies tried      : 1
% 3.07/1.48  
% 3.07/1.48  Timing (in seconds)
% 3.07/1.48  ----------------------
% 3.07/1.49  Preprocessing        : 0.33
% 3.07/1.49  Parsing              : 0.18
% 3.07/1.49  CNF conversion       : 0.02
% 3.07/1.49  Main loop            : 0.34
% 3.07/1.49  Inferencing          : 0.13
% 3.07/1.49  Reduction            : 0.11
% 3.07/1.49  Demodulation         : 0.08
% 3.07/1.49  BG Simplification    : 0.02
% 3.07/1.49  Subsumption          : 0.06
% 3.07/1.49  Abstraction          : 0.02
% 3.07/1.49  MUC search           : 0.00
% 3.07/1.49  Cooper               : 0.00
% 3.07/1.49  Total                : 0.70
% 3.07/1.49  Index Insertion      : 0.00
% 3.07/1.49  Index Deletion       : 0.00
% 3.07/1.49  Index Matching       : 0.00
% 3.07/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
