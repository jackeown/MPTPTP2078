%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:43 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 208 expanded)
%              Number of leaves         :   33 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 887 expanded)
%              Number of equality atoms :   38 ( 194 expanded)
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

tff(f_113,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_61,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_88,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_22,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_45,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_55,plain,(
    ! [A_50,B_49,F_46,C_48,E_45,D_47] :
      ( k1_partfun1(A_50,B_49,C_48,D_47,E_45,F_46) = k5_relat_1(E_45,F_46)
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_48,D_47)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ! [A_50,B_49,E_45] :
      ( k1_partfun1(A_50,B_49,'#skF_3','#skF_1',E_45,'#skF_5') = k5_relat_1(E_45,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ v1_funct_1(E_45) ) ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_87,plain,(
    ! [A_54,B_55,E_56] :
      ( k1_partfun1(A_54,B_55,'#skF_3','#skF_1',E_56,'#skF_5') = k5_relat_1(E_56,'#skF_5')
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_1(E_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_59])).

tff(c_90,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_96,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90])).

tff(c_20,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_112,plain,(
    ! [B_63,D_66,C_65,A_62,E_64] :
      ( k1_partfun1(A_62,B_63,B_63,C_65,D_66,E_64) = k8_funct_2(A_62,B_63,C_65,D_66,E_64)
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k2_relset_1(A_62,B_63,D_66),k1_relset_1(B_63,C_65,E_64))
      | ~ m1_subset_1(E_64,k1_zfmisc_1(k2_zfmisc_1(B_63,C_65)))
      | ~ v1_funct_1(E_64)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_2(D_66,A_62,B_63)
      | ~ v1_funct_1(D_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_112])).

tff(c_118,plain,
    ( k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_96,c_115])).

tff(c_119,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_123,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_123])).

tff(c_128,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_108,plain,(
    ! [E_61,A_60,D_59,C_57,B_58] :
      ( k1_funct_1(k5_relat_1(D_59,E_61),C_57) = k1_funct_1(E_61,k1_funct_1(D_59,C_57))
      | k1_xboole_0 = B_58
      | ~ r2_hidden(C_57,A_60)
      | ~ v1_funct_1(E_61)
      | ~ v1_relat_1(E_61)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_58)))
      | ~ v1_funct_2(D_59,A_60,B_58)
      | ~ v1_funct_1(D_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_134,plain,(
    ! [D_70,B_67,E_68,B_71,A_69] :
      ( k1_funct_1(k5_relat_1(D_70,E_68),A_69) = k1_funct_1(E_68,k1_funct_1(D_70,A_69))
      | k1_xboole_0 = B_67
      | ~ v1_funct_1(E_68)
      | ~ v1_relat_1(E_68)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(B_71,B_67)))
      | ~ v1_funct_2(D_70,B_71,B_67)
      | ~ v1_funct_1(D_70)
      | v1_xboole_0(B_71)
      | ~ m1_subset_1(A_69,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_136,plain,(
    ! [E_68,A_69] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_68),A_69) = k1_funct_1(E_68,k1_funct_1('#skF_4',A_69))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_68)
      | ~ v1_relat_1(E_68)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_69,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_141,plain,(
    ! [E_68,A_69] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_68),A_69) = k1_funct_1(E_68,k1_funct_1('#skF_4',A_69))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_68)
      | ~ v1_relat_1(E_68)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_69,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_136])).

tff(c_142,plain,(
    ! [E_68,A_69] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_68),A_69) = k1_funct_1(E_68,k1_funct_1('#skF_4',A_69))
      | ~ v1_funct_1(E_68)
      | ~ v1_relat_1(E_68)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_69,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_141])).

tff(c_147,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_35,plain,(
    ! [B_37,A_38] :
      ( ~ v1_xboole_0(B_37)
      | B_37 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_147,c_38])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_150])).

tff(c_159,plain,(
    ! [E_72,A_73] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_72),A_73) = k1_funct_1(E_72,k1_funct_1('#skF_4',A_73))
      | ~ v1_funct_1(E_72)
      | ~ v1_relat_1(E_72)
      | ~ m1_subset_1(A_73,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_127,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_16,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_129,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_16])).

tff(c_165,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_129])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_53,c_26,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.26  
% 2.20/1.26  %Foreground sorts:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Background operators:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Foreground operators:
% 2.20/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.20/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.20/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.26  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.26  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.20/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.20/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.26  
% 2.20/1.28  tff(f_113, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.20/1.28  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.20/1.28  tff(f_71, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.20/1.28  tff(f_61, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.20/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.20/1.28  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.20/1.28  tff(f_88, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.20/1.28  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.20/1.28  tff(c_22, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_45, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.20/1.28  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.20/1.28  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_34, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_55, plain, (![A_50, B_49, F_46, C_48, E_45, D_47]: (k1_partfun1(A_50, B_49, C_48, D_47, E_45, F_46)=k5_relat_1(E_45, F_46) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_48, D_47))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.20/1.28  tff(c_59, plain, (![A_50, B_49, E_45]: (k1_partfun1(A_50, B_49, '#skF_3', '#skF_1', E_45, '#skF_5')=k5_relat_1(E_45, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~v1_funct_1(E_45))), inference(resolution, [status(thm)], [c_24, c_55])).
% 2.20/1.28  tff(c_87, plain, (![A_54, B_55, E_56]: (k1_partfun1(A_54, B_55, '#skF_3', '#skF_1', E_56, '#skF_5')=k5_relat_1(E_56, '#skF_5') | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_1(E_56))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_59])).
% 2.20/1.28  tff(c_90, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_87])).
% 2.20/1.28  tff(c_96, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_90])).
% 2.20/1.28  tff(c_20, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_112, plain, (![B_63, D_66, C_65, A_62, E_64]: (k1_partfun1(A_62, B_63, B_63, C_65, D_66, E_64)=k8_funct_2(A_62, B_63, C_65, D_66, E_64) | k1_xboole_0=B_63 | ~r1_tarski(k2_relset_1(A_62, B_63, D_66), k1_relset_1(B_63, C_65, E_64)) | ~m1_subset_1(E_64, k1_zfmisc_1(k2_zfmisc_1(B_63, C_65))) | ~v1_funct_1(E_64) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_2(D_66, A_62, B_63) | ~v1_funct_1(D_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.20/1.28  tff(c_115, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_112])).
% 2.20/1.28  tff(c_118, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_96, c_115])).
% 2.20/1.28  tff(c_119, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_118])).
% 2.20/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.20/1.28  tff(c_123, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2])).
% 2.20/1.28  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_123])).
% 2.20/1.28  tff(c_128, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_118])).
% 2.20/1.28  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.28  tff(c_108, plain, (![E_61, A_60, D_59, C_57, B_58]: (k1_funct_1(k5_relat_1(D_59, E_61), C_57)=k1_funct_1(E_61, k1_funct_1(D_59, C_57)) | k1_xboole_0=B_58 | ~r2_hidden(C_57, A_60) | ~v1_funct_1(E_61) | ~v1_relat_1(E_61) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_58))) | ~v1_funct_2(D_59, A_60, B_58) | ~v1_funct_1(D_59))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.20/1.28  tff(c_134, plain, (![D_70, B_67, E_68, B_71, A_69]: (k1_funct_1(k5_relat_1(D_70, E_68), A_69)=k1_funct_1(E_68, k1_funct_1(D_70, A_69)) | k1_xboole_0=B_67 | ~v1_funct_1(E_68) | ~v1_relat_1(E_68) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(B_71, B_67))) | ~v1_funct_2(D_70, B_71, B_67) | ~v1_funct_1(D_70) | v1_xboole_0(B_71) | ~m1_subset_1(A_69, B_71))), inference(resolution, [status(thm)], [c_6, c_108])).
% 2.20/1.28  tff(c_136, plain, (![E_68, A_69]: (k1_funct_1(k5_relat_1('#skF_4', E_68), A_69)=k1_funct_1(E_68, k1_funct_1('#skF_4', A_69)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_68) | ~v1_relat_1(E_68) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_69, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_134])).
% 2.20/1.28  tff(c_141, plain, (![E_68, A_69]: (k1_funct_1(k5_relat_1('#skF_4', E_68), A_69)=k1_funct_1(E_68, k1_funct_1('#skF_4', A_69)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_68) | ~v1_relat_1(E_68) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_69, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_136])).
% 2.20/1.28  tff(c_142, plain, (![E_68, A_69]: (k1_funct_1(k5_relat_1('#skF_4', E_68), A_69)=k1_funct_1(E_68, k1_funct_1('#skF_4', A_69)) | ~v1_funct_1(E_68) | ~v1_relat_1(E_68) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_69, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_128, c_141])).
% 2.20/1.28  tff(c_147, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_142])).
% 2.20/1.28  tff(c_35, plain, (![B_37, A_38]: (~v1_xboole_0(B_37) | B_37=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.20/1.28  tff(c_38, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_2, c_35])).
% 2.20/1.28  tff(c_150, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_147, c_38])).
% 2.20/1.28  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_150])).
% 2.20/1.28  tff(c_159, plain, (![E_72, A_73]: (k1_funct_1(k5_relat_1('#skF_4', E_72), A_73)=k1_funct_1(E_72, k1_funct_1('#skF_4', A_73)) | ~v1_funct_1(E_72) | ~v1_relat_1(E_72) | ~m1_subset_1(A_73, '#skF_2'))), inference(splitRight, [status(thm)], [c_142])).
% 2.20/1.28  tff(c_127, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_118])).
% 2.20/1.28  tff(c_16, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.20/1.28  tff(c_129, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_16])).
% 2.20/1.28  tff(c_165, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159, c_129])).
% 2.20/1.28  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_53, c_26, c_165])).
% 2.20/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  
% 2.20/1.28  Inference rules
% 2.20/1.28  ----------------------
% 2.20/1.28  #Ref     : 0
% 2.20/1.28  #Sup     : 29
% 2.20/1.28  #Fact    : 0
% 2.20/1.28  #Define  : 0
% 2.20/1.28  #Split   : 2
% 2.20/1.28  #Chain   : 0
% 2.20/1.28  #Close   : 0
% 2.20/1.28  
% 2.20/1.28  Ordering : KBO
% 2.20/1.28  
% 2.20/1.28  Simplification rules
% 2.20/1.28  ----------------------
% 2.20/1.28  #Subsume      : 0
% 2.20/1.28  #Demod        : 24
% 2.20/1.28  #Tautology    : 12
% 2.20/1.28  #SimpNegUnit  : 4
% 2.20/1.28  #BackRed      : 6
% 2.20/1.28  
% 2.20/1.28  #Partial instantiations: 0
% 2.20/1.28  #Strategies tried      : 1
% 2.20/1.28  
% 2.20/1.28  Timing (in seconds)
% 2.20/1.28  ----------------------
% 2.20/1.28  Preprocessing        : 0.33
% 2.20/1.28  Parsing              : 0.18
% 2.20/1.28  CNF conversion       : 0.02
% 2.20/1.28  Main loop            : 0.19
% 2.20/1.28  Inferencing          : 0.07
% 2.20/1.28  Reduction            : 0.06
% 2.20/1.28  Demodulation         : 0.04
% 2.20/1.28  BG Simplification    : 0.01
% 2.20/1.28  Subsumption          : 0.03
% 2.20/1.28  Abstraction          : 0.01
% 2.20/1.28  MUC search           : 0.00
% 2.20/1.28  Cooper               : 0.00
% 2.20/1.28  Total                : 0.56
% 2.20/1.28  Index Insertion      : 0.00
% 2.20/1.28  Index Deletion       : 0.00
% 2.20/1.28  Index Matching       : 0.00
% 2.20/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
