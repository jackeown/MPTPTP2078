%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:48 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 243 expanded)
%              Number of leaves         :   34 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 737 expanded)
%              Number of equality atoms :   19 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_539,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_547,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_539])).

tff(c_562,plain,(
    ! [A_139,B_140,C_141] :
      ( m1_subset_1(k1_relset_1(A_139,B_140,C_141),k1_zfmisc_1(A_139))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_583,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_562])).

tff(c_591,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_583])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_39,A_1] :
      ( r1_tarski(A_39,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_39,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_94,plain,(
    ! [A_39,A_1] :
      ( r1_tarski(A_39,A_1)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_91])).

tff(c_595,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_591,c_94])).

tff(c_82,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_22,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_119,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_123,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_119])).

tff(c_154,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k1_relset_1(A_57,B_58,C_59),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_154])).

tff(c_178,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_172])).

tff(c_182,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_94])).

tff(c_20,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_31] :
      ( v1_funct_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_63,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_67,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_63])).

tff(c_70,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_67])).

tff(c_71,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_71])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_74])).

tff(c_80,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_128,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_131,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_133,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_131])).

tff(c_24,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_198,plain,(
    ! [B_65,A_66] :
      ( v1_funct_2(B_65,k1_relat_1(B_65),A_66)
      | ~ r1_tarski(k2_relat_1(B_65),A_66)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_332,plain,(
    ! [A_93,A_94] :
      ( v1_funct_2(k2_funct_1(A_93),k2_relat_1(A_93),A_94)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_93)),A_94)
      | ~ v1_funct_1(k2_funct_1(A_93))
      | ~ v1_relat_1(k2_funct_1(A_93))
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_198])).

tff(c_335,plain,(
    ! [A_94] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_94)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_94)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_332])).

tff(c_340,plain,(
    ! [A_94] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_94)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_94)
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_44,c_80,c_335])).

tff(c_341,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_344,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_341])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_344])).

tff(c_350,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_202,plain,(
    ! [B_67,A_68] :
      ( m1_subset_1(B_67,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_67),A_68)))
      | ~ r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_422,plain,(
    ! [A_122,A_123] :
      ( m1_subset_1(k2_funct_1(A_122),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_122),A_123)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_122)),A_123)
      | ~ v1_funct_1(k2_funct_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_202])).

tff(c_439,plain,(
    ! [A_123] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_123)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_123)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_422])).

tff(c_450,plain,(
    ! [A_124] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_124)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_44,c_350,c_80,c_439])).

tff(c_79,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_95,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_472,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_450,c_95])).

tff(c_484,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_472])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_44,c_182,c_484])).

tff(c_489,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_26,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_493,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_489,c_26])).

tff(c_521,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_527,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_521])).

tff(c_530,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_527])).

tff(c_596,plain,(
    ! [B_142,A_143] :
      ( v1_funct_2(B_142,k1_relat_1(B_142),A_143)
      | ~ r1_tarski(k2_relat_1(B_142),A_143)
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_803,plain,(
    ! [A_186,A_187] :
      ( v1_funct_2(k2_funct_1(A_186),k2_relat_1(A_186),A_187)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_186)),A_187)
      | ~ v1_funct_1(k2_funct_1(A_186))
      | ~ v1_relat_1(k2_funct_1(A_186))
      | ~ v2_funct_1(A_186)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_596])).

tff(c_806,plain,(
    ! [A_187] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_187)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_187)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_803])).

tff(c_817,plain,(
    ! [A_192] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_192)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_44,c_493,c_80,c_806])).

tff(c_824,plain,(
    ! [A_192] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_192)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_192)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_817])).

tff(c_828,plain,(
    ! [A_193] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_193)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_44,c_824])).

tff(c_488,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_831,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_828,c_488])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.59  
% 3.06/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.59  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.06/1.59  
% 3.06/1.59  %Foreground sorts:
% 3.06/1.59  
% 3.06/1.59  
% 3.06/1.59  %Background operators:
% 3.06/1.59  
% 3.06/1.59  
% 3.06/1.59  %Foreground operators:
% 3.06/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.06/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.06/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.06/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.59  
% 3.06/1.61  tff(f_104, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.06/1.61  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.06/1.61  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.06/1.61  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.06/1.61  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.06/1.61  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.06/1.61  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.06/1.61  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.06/1.61  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.06/1.61  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.06/1.61  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.06/1.61  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.06/1.61  tff(c_539, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.61  tff(c_547, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_539])).
% 3.06/1.61  tff(c_562, plain, (![A_139, B_140, C_141]: (m1_subset_1(k1_relset_1(A_139, B_140, C_141), k1_zfmisc_1(A_139)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.61  tff(c_583, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_547, c_562])).
% 3.06/1.61  tff(c_591, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_583])).
% 3.06/1.61  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.61  tff(c_87, plain, (![A_39, B_40]: (r2_hidden(A_39, B_40) | v1_xboole_0(B_40) | ~m1_subset_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.61  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.61  tff(c_91, plain, (![A_39, A_1]: (r1_tarski(A_39, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_39, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_87, c_2])).
% 3.06/1.61  tff(c_94, plain, (![A_39, A_1]: (r1_tarski(A_39, A_1) | ~m1_subset_1(A_39, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_91])).
% 3.06/1.61  tff(c_595, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_591, c_94])).
% 3.06/1.61  tff(c_82, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.06/1.61  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_82])).
% 3.06/1.61  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.06/1.61  tff(c_44, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.06/1.61  tff(c_22, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.61  tff(c_119, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.61  tff(c_123, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_119])).
% 3.06/1.61  tff(c_154, plain, (![A_57, B_58, C_59]: (m1_subset_1(k1_relset_1(A_57, B_58, C_59), k1_zfmisc_1(A_57)) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.61  tff(c_172, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_154])).
% 3.06/1.61  tff(c_178, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_172])).
% 3.06/1.61  tff(c_182, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_178, c_94])).
% 3.06/1.61  tff(c_20, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.61  tff(c_64, plain, (![A_31]: (v1_funct_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.61  tff(c_40, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.06/1.61  tff(c_63, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.06/1.61  tff(c_67, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_63])).
% 3.06/1.61  tff(c_70, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_67])).
% 3.06/1.61  tff(c_71, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.06/1.61  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_71])).
% 3.06/1.61  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_74])).
% 3.06/1.61  tff(c_80, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_40])).
% 3.06/1.61  tff(c_42, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.06/1.61  tff(c_128, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.06/1.61  tff(c_131, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_128])).
% 3.06/1.61  tff(c_133, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_131])).
% 3.06/1.61  tff(c_24, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.61  tff(c_198, plain, (![B_65, A_66]: (v1_funct_2(B_65, k1_relat_1(B_65), A_66) | ~r1_tarski(k2_relat_1(B_65), A_66) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.61  tff(c_332, plain, (![A_93, A_94]: (v1_funct_2(k2_funct_1(A_93), k2_relat_1(A_93), A_94) | ~r1_tarski(k2_relat_1(k2_funct_1(A_93)), A_94) | ~v1_funct_1(k2_funct_1(A_93)) | ~v1_relat_1(k2_funct_1(A_93)) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_24, c_198])).
% 3.06/1.61  tff(c_335, plain, (![A_94]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_94) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_94) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_332])).
% 3.06/1.61  tff(c_340, plain, (![A_94]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_94) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_94) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_44, c_80, c_335])).
% 3.06/1.61  tff(c_341, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_340])).
% 3.06/1.61  tff(c_344, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_341])).
% 3.06/1.61  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_344])).
% 3.06/1.61  tff(c_350, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_340])).
% 3.06/1.61  tff(c_202, plain, (![B_67, A_68]: (m1_subset_1(B_67, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_67), A_68))) | ~r1_tarski(k2_relat_1(B_67), A_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.61  tff(c_422, plain, (![A_122, A_123]: (m1_subset_1(k2_funct_1(A_122), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_122), A_123))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_122)), A_123) | ~v1_funct_1(k2_funct_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_24, c_202])).
% 3.06/1.61  tff(c_439, plain, (![A_123]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_123))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_123) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_422])).
% 3.06/1.61  tff(c_450, plain, (![A_124]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_124))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_124))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_44, c_350, c_80, c_439])).
% 3.06/1.61  tff(c_79, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_40])).
% 3.06/1.61  tff(c_95, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_79])).
% 3.06/1.61  tff(c_472, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), '#skF_3')), inference(resolution, [status(thm)], [c_450, c_95])).
% 3.06/1.61  tff(c_484, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22, c_472])).
% 3.06/1.61  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_44, c_182, c_484])).
% 3.06/1.61  tff(c_489, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_79])).
% 3.06/1.61  tff(c_26, plain, (![C_13, A_11, B_12]: (v1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.06/1.61  tff(c_493, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_489, c_26])).
% 3.06/1.61  tff(c_521, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.06/1.61  tff(c_527, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_521])).
% 3.06/1.61  tff(c_530, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_527])).
% 3.06/1.61  tff(c_596, plain, (![B_142, A_143]: (v1_funct_2(B_142, k1_relat_1(B_142), A_143) | ~r1_tarski(k2_relat_1(B_142), A_143) | ~v1_funct_1(B_142) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.61  tff(c_803, plain, (![A_186, A_187]: (v1_funct_2(k2_funct_1(A_186), k2_relat_1(A_186), A_187) | ~r1_tarski(k2_relat_1(k2_funct_1(A_186)), A_187) | ~v1_funct_1(k2_funct_1(A_186)) | ~v1_relat_1(k2_funct_1(A_186)) | ~v2_funct_1(A_186) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(superposition, [status(thm), theory('equality')], [c_24, c_596])).
% 3.06/1.61  tff(c_806, plain, (![A_187]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_187) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_187) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_530, c_803])).
% 3.06/1.61  tff(c_817, plain, (![A_192]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_192) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_192))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_44, c_493, c_80, c_806])).
% 3.06/1.61  tff(c_824, plain, (![A_192]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_192) | ~r1_tarski(k1_relat_1('#skF_5'), A_192) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_817])).
% 3.06/1.61  tff(c_828, plain, (![A_193]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_193) | ~r1_tarski(k1_relat_1('#skF_5'), A_193))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_44, c_824])).
% 3.06/1.61  tff(c_488, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_79])).
% 3.06/1.61  tff(c_831, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_828, c_488])).
% 3.06/1.61  tff(c_835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_595, c_831])).
% 3.06/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.61  
% 3.06/1.61  Inference rules
% 3.06/1.61  ----------------------
% 3.06/1.61  #Ref     : 0
% 3.06/1.61  #Sup     : 166
% 3.06/1.61  #Fact    : 0
% 3.06/1.61  #Define  : 0
% 3.06/1.61  #Split   : 7
% 3.06/1.61  #Chain   : 0
% 3.06/1.61  #Close   : 0
% 3.06/1.61  
% 3.06/1.61  Ordering : KBO
% 3.06/1.61  
% 3.06/1.61  Simplification rules
% 3.06/1.61  ----------------------
% 3.06/1.61  #Subsume      : 11
% 3.06/1.61  #Demod        : 80
% 3.06/1.61  #Tautology    : 50
% 3.06/1.61  #SimpNegUnit  : 9
% 3.06/1.61  #BackRed      : 1
% 3.06/1.61  
% 3.06/1.61  #Partial instantiations: 0
% 3.06/1.61  #Strategies tried      : 1
% 3.06/1.61  
% 3.06/1.61  Timing (in seconds)
% 3.06/1.61  ----------------------
% 3.06/1.62  Preprocessing        : 0.32
% 3.06/1.62  Parsing              : 0.17
% 3.06/1.62  CNF conversion       : 0.02
% 3.06/1.62  Main loop            : 0.39
% 3.06/1.62  Inferencing          : 0.16
% 3.06/1.62  Reduction            : 0.10
% 3.06/1.62  Demodulation         : 0.07
% 3.06/1.62  BG Simplification    : 0.02
% 3.06/1.62  Subsumption          : 0.07
% 3.06/1.62  Abstraction          : 0.02
% 3.06/1.62  MUC search           : 0.00
% 3.06/1.62  Cooper               : 0.00
% 3.06/1.62  Total                : 0.75
% 3.06/1.62  Index Insertion      : 0.00
% 3.06/1.62  Index Deletion       : 0.00
% 3.06/1.62  Index Matching       : 0.00
% 3.06/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
