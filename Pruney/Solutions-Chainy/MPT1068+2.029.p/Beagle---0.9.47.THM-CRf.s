%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:44 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 208 expanded)
%              Number of leaves         :   34 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 887 expanded)
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

tff(f_114,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_62,axiom,(
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

tff(f_89,axiom,(
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

tff(c_24,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_45,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_57,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,(
    ! [A_50,B_47,F_48,D_46,C_45,E_49] :
      ( k1_partfun1(A_50,B_47,C_45,D_46,E_49,F_48) = k5_relat_1(E_49,F_48)
      | ~ m1_subset_1(F_48,k1_zfmisc_1(k2_zfmisc_1(C_45,D_46)))
      | ~ v1_funct_1(F_48)
      | ~ m1_subset_1(E_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_47)))
      | ~ v1_funct_1(E_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,(
    ! [A_50,B_47,E_49] :
      ( k1_partfun1(A_50,B_47,'#skF_3','#skF_1',E_49,'#skF_5') = k5_relat_1(E_49,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_47)))
      | ~ v1_funct_1(E_49) ) ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_90,plain,(
    ! [A_54,B_55,E_56] :
      ( k1_partfun1(A_54,B_55,'#skF_3','#skF_1',E_56,'#skF_5') = k5_relat_1(E_56,'#skF_5')
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_1(E_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_93,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_90])).

tff(c_99,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_93])).

tff(c_22,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_115,plain,(
    ! [B_62,A_66,C_64,E_63,D_65] :
      ( k1_partfun1(A_66,B_62,B_62,C_64,D_65,E_63) = k8_funct_2(A_66,B_62,C_64,D_65,E_63)
      | k1_xboole_0 = B_62
      | ~ r1_tarski(k2_relset_1(A_66,B_62,D_65),k1_relset_1(B_62,C_64,E_63))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(B_62,C_64)))
      | ~ v1_funct_1(E_63)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_62)))
      | ~ v1_funct_2(D_65,A_66,B_62)
      | ~ v1_funct_1(D_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_118,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_121,plain,
    ( k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_99,c_118])).

tff(c_122,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_126,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_126])).

tff(c_131,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [A_57,E_59,B_61,C_60,D_58] :
      ( k1_funct_1(k5_relat_1(D_58,E_59),C_60) = k1_funct_1(E_59,k1_funct_1(D_58,C_60))
      | k1_xboole_0 = B_61
      | ~ r2_hidden(C_60,A_57)
      | ~ v1_funct_1(E_59)
      | ~ v1_relat_1(E_59)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_61)))
      | ~ v1_funct_2(D_58,A_57,B_61)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_137,plain,(
    ! [B_70,D_67,B_68,E_71,A_69] :
      ( k1_funct_1(k5_relat_1(D_67,E_71),A_69) = k1_funct_1(E_71,k1_funct_1(D_67,A_69))
      | k1_xboole_0 = B_70
      | ~ v1_funct_1(E_71)
      | ~ v1_relat_1(E_71)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_68,B_70)))
      | ~ v1_funct_2(D_67,B_68,B_70)
      | ~ v1_funct_1(D_67)
      | v1_xboole_0(B_68)
      | ~ m1_subset_1(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_139,plain,(
    ! [E_71,A_69] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_71),A_69) = k1_funct_1(E_71,k1_funct_1('#skF_4',A_69))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_71)
      | ~ v1_relat_1(E_71)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_69,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_137])).

tff(c_144,plain,(
    ! [E_71,A_69] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_71),A_69) = k1_funct_1(E_71,k1_funct_1('#skF_4',A_69))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_71)
      | ~ v1_relat_1(E_71)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_69,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_139])).

tff(c_145,plain,(
    ! [E_71,A_69] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_71),A_69) = k1_funct_1(E_71,k1_funct_1('#skF_4',A_69))
      | ~ v1_funct_1(E_71)
      | ~ v1_relat_1(E_71)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_69,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_144])).

tff(c_150,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_153,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_153])).

tff(c_160,plain,(
    ! [E_72,A_73] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_72),A_73) = k1_funct_1(E_72,k1_funct_1('#skF_4',A_73))
      | ~ v1_funct_1(E_72)
      | ~ v1_relat_1(E_72)
      | ~ m1_subset_1(A_73,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_130,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_18,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_132,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_166,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_132])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_57,c_28,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.35  % CPULimit   : 60
% 0.21/0.35  % DateTime   : Tue Dec  1 19:22:35 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.32  
% 2.32/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.32  
% 2.32/1.32  %Foreground sorts:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Background operators:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Foreground operators:
% 2.32/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.32/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.32/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.32  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.32/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.32  
% 2.32/1.34  tff(f_114, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.32/1.34  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.32/1.34  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.32/1.34  tff(f_72, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.32/1.34  tff(f_62, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.32/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.32/1.34  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.32/1.34  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.32/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.32/1.34  tff(c_24, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.32/1.34  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_45, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.34  tff(c_51, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.32/1.34  tff(c_57, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_51])).
% 2.32/1.34  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_58, plain, (![A_50, B_47, F_48, D_46, C_45, E_49]: (k1_partfun1(A_50, B_47, C_45, D_46, E_49, F_48)=k5_relat_1(E_49, F_48) | ~m1_subset_1(F_48, k1_zfmisc_1(k2_zfmisc_1(C_45, D_46))) | ~v1_funct_1(F_48) | ~m1_subset_1(E_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_47))) | ~v1_funct_1(E_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.32/1.34  tff(c_62, plain, (![A_50, B_47, E_49]: (k1_partfun1(A_50, B_47, '#skF_3', '#skF_1', E_49, '#skF_5')=k5_relat_1(E_49, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_47))) | ~v1_funct_1(E_49))), inference(resolution, [status(thm)], [c_26, c_58])).
% 2.32/1.34  tff(c_90, plain, (![A_54, B_55, E_56]: (k1_partfun1(A_54, B_55, '#skF_3', '#skF_1', E_56, '#skF_5')=k5_relat_1(E_56, '#skF_5') | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_1(E_56))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_62])).
% 2.32/1.34  tff(c_93, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_90])).
% 2.32/1.34  tff(c_99, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_93])).
% 2.32/1.34  tff(c_22, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_115, plain, (![B_62, A_66, C_64, E_63, D_65]: (k1_partfun1(A_66, B_62, B_62, C_64, D_65, E_63)=k8_funct_2(A_66, B_62, C_64, D_65, E_63) | k1_xboole_0=B_62 | ~r1_tarski(k2_relset_1(A_66, B_62, D_65), k1_relset_1(B_62, C_64, E_63)) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(B_62, C_64))) | ~v1_funct_1(E_63) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_62))) | ~v1_funct_2(D_65, A_66, B_62) | ~v1_funct_1(D_65))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.34  tff(c_118, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_115])).
% 2.32/1.34  tff(c_121, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_99, c_118])).
% 2.32/1.34  tff(c_122, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_121])).
% 2.32/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.32/1.34  tff(c_126, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2])).
% 2.32/1.34  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_126])).
% 2.32/1.34  tff(c_131, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_121])).
% 2.32/1.34  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.32/1.34  tff(c_111, plain, (![A_57, E_59, B_61, C_60, D_58]: (k1_funct_1(k5_relat_1(D_58, E_59), C_60)=k1_funct_1(E_59, k1_funct_1(D_58, C_60)) | k1_xboole_0=B_61 | ~r2_hidden(C_60, A_57) | ~v1_funct_1(E_59) | ~v1_relat_1(E_59) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_61))) | ~v1_funct_2(D_58, A_57, B_61) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.32/1.34  tff(c_137, plain, (![B_70, D_67, B_68, E_71, A_69]: (k1_funct_1(k5_relat_1(D_67, E_71), A_69)=k1_funct_1(E_71, k1_funct_1(D_67, A_69)) | k1_xboole_0=B_70 | ~v1_funct_1(E_71) | ~v1_relat_1(E_71) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_68, B_70))) | ~v1_funct_2(D_67, B_68, B_70) | ~v1_funct_1(D_67) | v1_xboole_0(B_68) | ~m1_subset_1(A_69, B_68))), inference(resolution, [status(thm)], [c_6, c_111])).
% 2.32/1.34  tff(c_139, plain, (![E_71, A_69]: (k1_funct_1(k5_relat_1('#skF_4', E_71), A_69)=k1_funct_1(E_71, k1_funct_1('#skF_4', A_69)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_71) | ~v1_relat_1(E_71) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_69, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_137])).
% 2.32/1.34  tff(c_144, plain, (![E_71, A_69]: (k1_funct_1(k5_relat_1('#skF_4', E_71), A_69)=k1_funct_1(E_71, k1_funct_1('#skF_4', A_69)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_71) | ~v1_relat_1(E_71) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_69, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_139])).
% 2.32/1.34  tff(c_145, plain, (![E_71, A_69]: (k1_funct_1(k5_relat_1('#skF_4', E_71), A_69)=k1_funct_1(E_71, k1_funct_1('#skF_4', A_69)) | ~v1_funct_1(E_71) | ~v1_relat_1(E_71) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_69, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_131, c_144])).
% 2.32/1.34  tff(c_150, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_145])).
% 2.32/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.32/1.34  tff(c_153, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_150, c_4])).
% 2.32/1.34  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_153])).
% 2.32/1.34  tff(c_160, plain, (![E_72, A_73]: (k1_funct_1(k5_relat_1('#skF_4', E_72), A_73)=k1_funct_1(E_72, k1_funct_1('#skF_4', A_73)) | ~v1_funct_1(E_72) | ~v1_relat_1(E_72) | ~m1_subset_1(A_73, '#skF_2'))), inference(splitRight, [status(thm)], [c_145])).
% 2.32/1.34  tff(c_130, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_121])).
% 2.32/1.34  tff(c_18, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.32/1.34  tff(c_132, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_18])).
% 2.32/1.34  tff(c_166, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_160, c_132])).
% 2.32/1.34  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_57, c_28, c_166])).
% 2.32/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  Inference rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Ref     : 0
% 2.32/1.34  #Sup     : 27
% 2.32/1.34  #Fact    : 0
% 2.32/1.34  #Define  : 0
% 2.32/1.34  #Split   : 2
% 2.32/1.34  #Chain   : 0
% 2.32/1.34  #Close   : 0
% 2.32/1.34  
% 2.32/1.34  Ordering : KBO
% 2.32/1.34  
% 2.32/1.34  Simplification rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Subsume      : 0
% 2.32/1.34  #Demod        : 26
% 2.32/1.34  #Tautology    : 12
% 2.32/1.34  #SimpNegUnit  : 4
% 2.32/1.34  #BackRed      : 6
% 2.32/1.34  
% 2.32/1.34  #Partial instantiations: 0
% 2.32/1.34  #Strategies tried      : 1
% 2.32/1.34  
% 2.32/1.34  Timing (in seconds)
% 2.32/1.34  ----------------------
% 2.32/1.35  Preprocessing        : 0.34
% 2.32/1.35  Parsing              : 0.18
% 2.32/1.35  CNF conversion       : 0.03
% 2.32/1.35  Main loop            : 0.18
% 2.32/1.35  Inferencing          : 0.07
% 2.32/1.35  Reduction            : 0.06
% 2.32/1.35  Demodulation         : 0.04
% 2.32/1.35  BG Simplification    : 0.01
% 2.32/1.35  Subsumption          : 0.03
% 2.32/1.35  Abstraction          : 0.01
% 2.32/1.35  MUC search           : 0.00
% 2.32/1.35  Cooper               : 0.00
% 2.32/1.35  Total                : 0.56
% 2.32/1.35  Index Insertion      : 0.00
% 2.32/1.35  Index Deletion       : 0.00
% 2.32/1.35  Index Matching       : 0.00
% 2.32/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
