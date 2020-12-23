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
% DateTime   : Thu Dec  3 10:15:35 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 105 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 197 expanded)
%              Number of equality atoms :   30 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_229,plain,(
    ! [F_74,B_73,D_77,E_76,C_72,A_75] :
      ( k4_relset_1(A_75,B_73,C_72,D_77,E_76,F_74) = k5_relat_1(E_76,F_74)
      | ~ m1_subset_1(F_74,k1_zfmisc_1(k2_zfmisc_1(C_72,D_77)))
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_381,plain,(
    ! [A_96,B_97,E_98] :
      ( k4_relset_1(A_96,B_97,'#skF_3','#skF_3',E_98,'#skF_4') = k5_relat_1(E_98,'#skF_4')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(resolution,[status(thm)],[c_40,c_229])).

tff(c_402,plain,(
    k4_relset_1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4') = k5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_381])).

tff(c_32,plain,(
    k2_relset_1('#skF_3','#skF_3',k4_relset_1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_5','#skF_4')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_453,plain,(
    k2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_5','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_32])).

tff(c_73,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_36,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_99,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_102,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_99])).

tff(c_107,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_102])).

tff(c_82,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_124,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k1_relset_1(A_57,B_58,C_59),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_124])).

tff(c_153,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_145])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_42,A_1] :
      ( r1_tarski(A_42,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_42,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_63,plain,(
    ! [A_42,A_1] :
      ( r1_tarski(A_42,A_1)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_60])).

tff(c_167,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_63])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_34,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_105,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_99])).

tff(c_109,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_191,plain,(
    ! [B_69,A_70] :
      ( k2_relat_1(k5_relat_1(B_69,A_70)) = k2_relat_1(A_70)
      | ~ r1_tarski(k1_relat_1(A_70),k2_relat_1(B_69))
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_194,plain,(
    ! [A_70] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_70)) = k2_relat_1(A_70)
      | ~ r1_tarski(k1_relat_1(A_70),'#skF_3')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_191])).

tff(c_202,plain,(
    ! [A_71] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_71)) = k2_relat_1(A_71)
      | ~ r1_tarski(k1_relat_1(A_71),'#skF_3')
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_194])).

tff(c_205,plain,
    ( k2_relat_1(k5_relat_1('#skF_5','#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_202])).

tff(c_211,plain,(
    k2_relat_1(k5_relat_1('#skF_5','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_107,c_205])).

tff(c_24,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( m1_subset_1(k4_relset_1(A_18,B_19,C_20,D_21,E_22,F_23),k1_zfmisc_1(k2_zfmisc_1(A_18,D_21)))
      | ~ m1_subset_1(F_23,k1_zfmisc_1(k2_zfmisc_1(C_20,D_21)))
      | ~ m1_subset_1(E_22,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_457,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_24])).

tff(c_461,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_457])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_475,plain,(
    k2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_5','#skF_4')) = k2_relat_1(k5_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_461,c_28])).

tff(c_490,plain,(
    k2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_5','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_475])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.77/1.41  
% 2.77/1.41  %Foreground sorts:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Background operators:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Foreground operators:
% 2.77/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.41  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.41  
% 2.77/1.43  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_2)).
% 2.77/1.43  tff(f_78, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.77/1.43  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.77/1.43  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.77/1.43  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.77/1.43  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.77/1.43  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.77/1.43  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.77/1.43  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.77/1.43  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.77/1.43  tff(f_64, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.77/1.43  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.43  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.43  tff(c_229, plain, (![F_74, B_73, D_77, E_76, C_72, A_75]: (k4_relset_1(A_75, B_73, C_72, D_77, E_76, F_74)=k5_relat_1(E_76, F_74) | ~m1_subset_1(F_74, k1_zfmisc_1(k2_zfmisc_1(C_72, D_77))) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_73))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.77/1.43  tff(c_381, plain, (![A_96, B_97, E_98]: (k4_relset_1(A_96, B_97, '#skF_3', '#skF_3', E_98, '#skF_4')=k5_relat_1(E_98, '#skF_4') | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(resolution, [status(thm)], [c_40, c_229])).
% 2.77/1.43  tff(c_402, plain, (k4_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4')=k5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_381])).
% 2.77/1.43  tff(c_32, plain, (k2_relset_1('#skF_3', '#skF_3', k4_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_5', '#skF_4'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.43  tff(c_453, plain, (k2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_5', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_32])).
% 2.77/1.43  tff(c_73, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.43  tff(c_80, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_73])).
% 2.77/1.43  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.43  tff(c_99, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.43  tff(c_102, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_99])).
% 2.77/1.43  tff(c_107, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_102])).
% 2.77/1.43  tff(c_82, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.43  tff(c_89, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_82])).
% 2.77/1.43  tff(c_124, plain, (![A_57, B_58, C_59]: (m1_subset_1(k1_relset_1(A_57, B_58, C_59), k1_zfmisc_1(A_57)) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.43  tff(c_145, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_89, c_124])).
% 2.77/1.43  tff(c_153, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_145])).
% 2.77/1.43  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.43  tff(c_56, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | v1_xboole_0(B_43) | ~m1_subset_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.43  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.43  tff(c_60, plain, (![A_42, A_1]: (r1_tarski(A_42, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_42, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_56, c_2])).
% 2.77/1.43  tff(c_63, plain, (![A_42, A_1]: (r1_tarski(A_42, A_1) | ~m1_subset_1(A_42, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_60])).
% 2.77/1.43  tff(c_167, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_153, c_63])).
% 2.77/1.43  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_73])).
% 2.77/1.43  tff(c_34, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.43  tff(c_105, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_99])).
% 2.77/1.43  tff(c_109, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_105])).
% 2.77/1.43  tff(c_191, plain, (![B_69, A_70]: (k2_relat_1(k5_relat_1(B_69, A_70))=k2_relat_1(A_70) | ~r1_tarski(k1_relat_1(A_70), k2_relat_1(B_69)) | ~v1_relat_1(B_69) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.77/1.43  tff(c_194, plain, (![A_70]: (k2_relat_1(k5_relat_1('#skF_5', A_70))=k2_relat_1(A_70) | ~r1_tarski(k1_relat_1(A_70), '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_109, c_191])).
% 2.77/1.43  tff(c_202, plain, (![A_71]: (k2_relat_1(k5_relat_1('#skF_5', A_71))=k2_relat_1(A_71) | ~r1_tarski(k1_relat_1(A_71), '#skF_3') | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_194])).
% 2.77/1.43  tff(c_205, plain, (k2_relat_1(k5_relat_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_167, c_202])).
% 2.77/1.43  tff(c_211, plain, (k2_relat_1(k5_relat_1('#skF_5', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_107, c_205])).
% 2.77/1.43  tff(c_24, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (m1_subset_1(k4_relset_1(A_18, B_19, C_20, D_21, E_22, F_23), k1_zfmisc_1(k2_zfmisc_1(A_18, D_21))) | ~m1_subset_1(F_23, k1_zfmisc_1(k2_zfmisc_1(C_20, D_21))) | ~m1_subset_1(E_22, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.43  tff(c_457, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_402, c_24])).
% 2.77/1.43  tff(c_461, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_457])).
% 2.77/1.43  tff(c_28, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.43  tff(c_475, plain, (k2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_5', '#skF_4'))=k2_relat_1(k5_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_461, c_28])).
% 2.77/1.43  tff(c_490, plain, (k2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_5', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_475])).
% 2.77/1.43  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_453, c_490])).
% 2.77/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  Inference rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Ref     : 0
% 2.77/1.43  #Sup     : 117
% 2.77/1.43  #Fact    : 0
% 2.77/1.43  #Define  : 0
% 2.77/1.43  #Split   : 0
% 2.77/1.43  #Chain   : 0
% 2.77/1.43  #Close   : 0
% 2.77/1.43  
% 2.77/1.43  Ordering : KBO
% 2.77/1.43  
% 2.77/1.43  Simplification rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Subsume      : 1
% 2.77/1.43  #Demod        : 30
% 2.77/1.43  #Tautology    : 37
% 2.77/1.43  #SimpNegUnit  : 3
% 2.77/1.43  #BackRed      : 1
% 2.77/1.43  
% 2.77/1.43  #Partial instantiations: 0
% 2.77/1.43  #Strategies tried      : 1
% 2.77/1.43  
% 2.77/1.43  Timing (in seconds)
% 2.77/1.43  ----------------------
% 2.77/1.43  Preprocessing        : 0.34
% 2.77/1.43  Parsing              : 0.19
% 2.77/1.43  CNF conversion       : 0.02
% 2.77/1.43  Main loop            : 0.30
% 2.77/1.43  Inferencing          : 0.12
% 2.77/1.43  Reduction            : 0.08
% 2.77/1.43  Demodulation         : 0.05
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.43  Subsumption          : 0.05
% 2.77/1.43  Abstraction          : 0.02
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.67
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
