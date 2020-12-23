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
% DateTime   : Thu Dec  3 10:17:43 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 205 expanded)
%              Number of leaves         :   33 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 881 expanded)
%              Number of equality atoms :   37 ( 193 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_41,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_51,plain,(
    ! [A_46,C_47,F_42,D_43,E_45,B_44] :
      ( k1_partfun1(A_46,B_44,C_47,D_43,E_45,F_42) = k5_relat_1(E_45,F_42)
      | ~ m1_subset_1(F_42,k1_zfmisc_1(k2_zfmisc_1(C_47,D_43)))
      | ~ v1_funct_1(F_42)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_44)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,(
    ! [A_46,B_44,E_45] :
      ( k1_partfun1(A_46,B_44,'#skF_3','#skF_1',E_45,'#skF_5') = k5_relat_1(E_45,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_44)))
      | ~ v1_funct_1(E_45) ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_62,plain,(
    ! [A_48,B_49,E_50] :
      ( k1_partfun1(A_48,B_49,'#skF_3','#skF_1',E_50,'#skF_5') = k5_relat_1(E_50,'#skF_5')
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(E_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_53])).

tff(c_68,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_74,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_20,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_120,plain,(
    ! [D_64,A_67,E_68,C_66,B_65] :
      ( k1_partfun1(A_67,B_65,B_65,C_66,D_64,E_68) = k8_funct_2(A_67,B_65,C_66,D_64,E_68)
      | k1_xboole_0 = B_65
      | ~ r1_tarski(k2_relset_1(A_67,B_65,D_64),k1_relset_1(B_65,C_66,E_68))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(B_65,C_66)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_67,B_65)))
      | ~ v1_funct_2(D_64,A_67,B_65)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_123,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_120])).

tff(c_126,plain,
    ( k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_74,c_123])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_132,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_132])).

tff(c_137,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_104,plain,(
    ! [A_56,E_57,C_54,B_55,D_58] :
      ( k1_funct_1(k5_relat_1(D_58,E_57),C_54) = k1_funct_1(E_57,k1_funct_1(D_58,C_54))
      | k1_xboole_0 = B_55
      | ~ r2_hidden(C_54,A_56)
      | ~ v1_funct_1(E_57)
      | ~ v1_relat_1(E_57)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55)))
      | ~ v1_funct_2(D_58,A_56,B_55)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_108,plain,(
    ! [B_62,D_59,A_63,B_61,E_60] :
      ( k1_funct_1(k5_relat_1(D_59,E_60),A_63) = k1_funct_1(E_60,k1_funct_1(D_59,A_63))
      | k1_xboole_0 = B_62
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(B_61,B_62)))
      | ~ v1_funct_2(D_59,B_61,B_62)
      | ~ v1_funct_1(D_59)
      | v1_xboole_0(B_61)
      | ~ m1_subset_1(A_63,B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_112,plain,(
    ! [E_60,A_63] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_60),A_63) = k1_funct_1(E_60,k1_funct_1('#skF_4',A_63))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_63,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_119,plain,(
    ! [E_60,A_63] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_60),A_63) = k1_funct_1(E_60,k1_funct_1('#skF_4',A_63))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_63,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_112])).

tff(c_144,plain,(
    ! [E_60,A_63] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_60),A_63) = k1_funct_1(E_60,k1_funct_1('#skF_4',A_63))
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_63,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_119])).

tff(c_145,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_145,c_4])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_148])).

tff(c_155,plain,(
    ! [E_69,A_70] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_69),A_70) = k1_funct_1(E_69,k1_funct_1('#skF_4',A_70))
      | ~ v1_funct_1(E_69)
      | ~ v1_relat_1(E_69)
      | ~ m1_subset_1(A_70,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_136,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_16,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_139,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_16])).

tff(c_161,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_139])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_48,c_26,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:35 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.36  
% 2.24/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.36  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.36  
% 2.24/1.36  %Foreground sorts:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Background operators:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Foreground operators:
% 2.24/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.24/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.36  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.36  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.36  
% 2.43/1.38  tff(f_109, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.43/1.38  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.43/1.38  tff(f_67, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.43/1.38  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.43/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.43/1.38  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.43/1.38  tff(f_84, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.43/1.38  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.43/1.38  tff(c_22, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_41, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.38  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.43/1.38  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_34, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_51, plain, (![A_46, C_47, F_42, D_43, E_45, B_44]: (k1_partfun1(A_46, B_44, C_47, D_43, E_45, F_42)=k5_relat_1(E_45, F_42) | ~m1_subset_1(F_42, k1_zfmisc_1(k2_zfmisc_1(C_47, D_43))) | ~v1_funct_1(F_42) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_44))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.38  tff(c_53, plain, (![A_46, B_44, E_45]: (k1_partfun1(A_46, B_44, '#skF_3', '#skF_1', E_45, '#skF_5')=k5_relat_1(E_45, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_44))) | ~v1_funct_1(E_45))), inference(resolution, [status(thm)], [c_24, c_51])).
% 2.43/1.38  tff(c_62, plain, (![A_48, B_49, E_50]: (k1_partfun1(A_48, B_49, '#skF_3', '#skF_1', E_50, '#skF_5')=k5_relat_1(E_50, '#skF_5') | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1(E_50))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_53])).
% 2.43/1.38  tff(c_68, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_62])).
% 2.43/1.38  tff(c_74, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 2.43/1.38  tff(c_20, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_120, plain, (![D_64, A_67, E_68, C_66, B_65]: (k1_partfun1(A_67, B_65, B_65, C_66, D_64, E_68)=k8_funct_2(A_67, B_65, C_66, D_64, E_68) | k1_xboole_0=B_65 | ~r1_tarski(k2_relset_1(A_67, B_65, D_64), k1_relset_1(B_65, C_66, E_68)) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(B_65, C_66))) | ~v1_funct_1(E_68) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_67, B_65))) | ~v1_funct_2(D_64, A_67, B_65) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.38  tff(c_123, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_120])).
% 2.43/1.38  tff(c_126, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_74, c_123])).
% 2.43/1.38  tff(c_127, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_126])).
% 2.43/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.43/1.38  tff(c_132, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2])).
% 2.43/1.38  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_132])).
% 2.43/1.38  tff(c_137, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_126])).
% 2.43/1.38  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.43/1.38  tff(c_104, plain, (![A_56, E_57, C_54, B_55, D_58]: (k1_funct_1(k5_relat_1(D_58, E_57), C_54)=k1_funct_1(E_57, k1_funct_1(D_58, C_54)) | k1_xboole_0=B_55 | ~r2_hidden(C_54, A_56) | ~v1_funct_1(E_57) | ~v1_relat_1(E_57) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))) | ~v1_funct_2(D_58, A_56, B_55) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.43/1.38  tff(c_108, plain, (![B_62, D_59, A_63, B_61, E_60]: (k1_funct_1(k5_relat_1(D_59, E_60), A_63)=k1_funct_1(E_60, k1_funct_1(D_59, A_63)) | k1_xboole_0=B_62 | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(B_61, B_62))) | ~v1_funct_2(D_59, B_61, B_62) | ~v1_funct_1(D_59) | v1_xboole_0(B_61) | ~m1_subset_1(A_63, B_61))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.43/1.38  tff(c_112, plain, (![E_60, A_63]: (k1_funct_1(k5_relat_1('#skF_4', E_60), A_63)=k1_funct_1(E_60, k1_funct_1('#skF_4', A_63)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_63, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_108])).
% 2.43/1.38  tff(c_119, plain, (![E_60, A_63]: (k1_funct_1(k5_relat_1('#skF_4', E_60), A_63)=k1_funct_1(E_60, k1_funct_1('#skF_4', A_63)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_63, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_112])).
% 2.43/1.38  tff(c_144, plain, (![E_60, A_63]: (k1_funct_1(k5_relat_1('#skF_4', E_60), A_63)=k1_funct_1(E_60, k1_funct_1('#skF_4', A_63)) | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_63, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_137, c_119])).
% 2.43/1.38  tff(c_145, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_144])).
% 2.43/1.38  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.43/1.38  tff(c_148, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_145, c_4])).
% 2.43/1.38  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_148])).
% 2.43/1.38  tff(c_155, plain, (![E_69, A_70]: (k1_funct_1(k5_relat_1('#skF_4', E_69), A_70)=k1_funct_1(E_69, k1_funct_1('#skF_4', A_70)) | ~v1_funct_1(E_69) | ~v1_relat_1(E_69) | ~m1_subset_1(A_70, '#skF_2'))), inference(splitRight, [status(thm)], [c_144])).
% 2.43/1.38  tff(c_136, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_126])).
% 2.43/1.38  tff(c_16, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.43/1.38  tff(c_139, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_16])).
% 2.43/1.38  tff(c_161, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_155, c_139])).
% 2.43/1.38  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_48, c_26, c_161])).
% 2.43/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  Inference rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Ref     : 0
% 2.43/1.38  #Sup     : 27
% 2.43/1.38  #Fact    : 0
% 2.43/1.38  #Define  : 0
% 2.43/1.38  #Split   : 3
% 2.43/1.38  #Chain   : 0
% 2.43/1.38  #Close   : 0
% 2.43/1.38  
% 2.43/1.38  Ordering : KBO
% 2.43/1.38  
% 2.43/1.38  Simplification rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Subsume      : 0
% 2.43/1.38  #Demod        : 25
% 2.43/1.38  #Tautology    : 12
% 2.43/1.38  #SimpNegUnit  : 4
% 2.43/1.38  #BackRed      : 7
% 2.43/1.38  
% 2.43/1.38  #Partial instantiations: 0
% 2.43/1.38  #Strategies tried      : 1
% 2.43/1.38  
% 2.43/1.38  Timing (in seconds)
% 2.43/1.38  ----------------------
% 2.43/1.39  Preprocessing        : 0.33
% 2.43/1.39  Parsing              : 0.19
% 2.43/1.39  CNF conversion       : 0.02
% 2.43/1.39  Main loop            : 0.22
% 2.43/1.39  Inferencing          : 0.08
% 2.43/1.39  Reduction            : 0.07
% 2.43/1.39  Demodulation         : 0.05
% 2.43/1.39  BG Simplification    : 0.01
% 2.43/1.39  Subsumption          : 0.04
% 2.43/1.39  Abstraction          : 0.01
% 2.43/1.39  MUC search           : 0.00
% 2.43/1.39  Cooper               : 0.00
% 2.43/1.39  Total                : 0.60
% 2.43/1.39  Index Insertion      : 0.00
% 2.43/1.39  Index Deletion       : 0.00
% 2.43/1.39  Index Matching       : 0.00
% 2.43/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
