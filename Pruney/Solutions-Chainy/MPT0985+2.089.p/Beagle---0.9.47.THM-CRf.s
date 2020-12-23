%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:40 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 149 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 419 expanded)
%              Number of equality atoms :   19 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_51,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8,plain,(
    ! [A_4] :
      ( v1_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_59,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_59])).

tff(c_64,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_89,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_82,plain,(
    ! [A_38] :
      ( k4_relat_1(A_38) = k2_funct_1(A_38)
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_88,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_85])).

tff(c_118,plain,(
    ! [A_41,B_42,C_43] :
      ( k3_relset_1(A_41,B_42,C_43) = k4_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_121,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_118])).

tff(c_123,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_121])).

tff(c_162,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k3_relset_1(A_51,B_52,C_53),k1_zfmisc_1(k2_zfmisc_1(B_52,A_51)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_180,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_162])).

tff(c_187,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_180])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_187])).

tff(c_191,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_16,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_207,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_191,c_16])).

tff(c_18,plain,(
    ! [C_11,B_10,A_9] :
      ( v5_relat_1(C_11,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_206,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_191,c_18])).

tff(c_217,plain,(
    ! [A_55] :
      ( k2_relat_1(k2_funct_1(A_55)) = k1_relat_1(A_55)
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_717,plain,(
    ! [A_98,A_99] :
      ( r1_tarski(k1_relat_1(A_98),A_99)
      | ~ v5_relat_1(k2_funct_1(A_98),A_99)
      | ~ v1_relat_1(k2_funct_1(A_98))
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_4])).

tff(c_720,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_717])).

tff(c_723,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_207,c_720])).

tff(c_12,plain,(
    ! [A_5] :
      ( k2_relat_1(k2_funct_1(A_5)) = k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_250,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_256,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_250])).

tff(c_259,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_256])).

tff(c_14,plain,(
    ! [A_5] :
      ( k1_relat_1(k2_funct_1(A_5)) = k2_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_260,plain,(
    ! [B_62,A_63] :
      ( v1_funct_2(B_62,k1_relat_1(B_62),A_63)
      | ~ r1_tarski(k2_relat_1(B_62),A_63)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1125,plain,(
    ! [A_127,A_128] :
      ( v1_funct_2(k2_funct_1(A_127),k2_relat_1(A_127),A_128)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_127)),A_128)
      | ~ v1_funct_1(k2_funct_1(A_127))
      | ~ v1_relat_1(k2_funct_1(A_127))
      | ~ v2_funct_1(A_127)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_260])).

tff(c_1128,plain,(
    ! [A_128] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_128)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_128)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_1125])).

tff(c_1134,plain,(
    ! [A_129] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_129)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_207,c_65,c_1128])).

tff(c_1137,plain,(
    ! [A_129] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_129)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_129)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1134])).

tff(c_1147,plain,(
    ! [A_130] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_130)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_38,c_1137])).

tff(c_190,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1150,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1147,c_190])).

tff(c_1154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_1150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.63  
% 3.88/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.88/1.63  
% 3.88/1.63  %Foreground sorts:
% 3.88/1.63  
% 3.88/1.63  
% 3.88/1.63  %Background operators:
% 3.88/1.63  
% 3.88/1.63  
% 3.88/1.63  %Foreground operators:
% 3.88/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.88/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.88/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.88/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.63  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.88/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.88/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.88/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.88/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.63  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.88/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.63  
% 3.88/1.65  tff(f_108, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.88/1.65  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.88/1.65  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.88/1.65  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.88/1.65  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.88/1.65  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.88/1.65  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.88/1.65  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.88/1.65  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.88/1.65  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.88/1.65  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.88/1.65  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.88/1.65  tff(c_51, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.88/1.65  tff(c_55, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_51])).
% 3.88/1.65  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.88/1.65  tff(c_38, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.88/1.65  tff(c_8, plain, (![A_4]: (v1_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.88/1.65  tff(c_34, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.88/1.65  tff(c_56, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 3.88/1.65  tff(c_59, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_56])).
% 3.88/1.65  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_59])).
% 3.88/1.65  tff(c_64, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_34])).
% 3.88/1.65  tff(c_89, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_64])).
% 3.88/1.65  tff(c_82, plain, (![A_38]: (k4_relat_1(A_38)=k2_funct_1(A_38) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.65  tff(c_85, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_82])).
% 3.88/1.65  tff(c_88, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_85])).
% 3.88/1.65  tff(c_118, plain, (![A_41, B_42, C_43]: (k3_relset_1(A_41, B_42, C_43)=k4_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.88/1.65  tff(c_121, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_118])).
% 3.88/1.65  tff(c_123, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_121])).
% 3.88/1.65  tff(c_162, plain, (![A_51, B_52, C_53]: (m1_subset_1(k3_relset_1(A_51, B_52, C_53), k1_zfmisc_1(k2_zfmisc_1(B_52, A_51))) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.88/1.65  tff(c_180, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_162])).
% 3.88/1.65  tff(c_187, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_180])).
% 3.88/1.65  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_187])).
% 3.88/1.65  tff(c_191, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 3.88/1.65  tff(c_16, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.88/1.65  tff(c_207, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_191, c_16])).
% 3.88/1.65  tff(c_18, plain, (![C_11, B_10, A_9]: (v5_relat_1(C_11, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.88/1.65  tff(c_206, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_191, c_18])).
% 3.88/1.65  tff(c_217, plain, (![A_55]: (k2_relat_1(k2_funct_1(A_55))=k1_relat_1(A_55) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.88/1.65  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.65  tff(c_717, plain, (![A_98, A_99]: (r1_tarski(k1_relat_1(A_98), A_99) | ~v5_relat_1(k2_funct_1(A_98), A_99) | ~v1_relat_1(k2_funct_1(A_98)) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_217, c_4])).
% 3.88/1.65  tff(c_720, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_206, c_717])).
% 3.88/1.65  tff(c_723, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_207, c_720])).
% 3.88/1.65  tff(c_12, plain, (![A_5]: (k2_relat_1(k2_funct_1(A_5))=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.88/1.65  tff(c_65, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_34])).
% 3.88/1.65  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.88/1.65  tff(c_250, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.88/1.65  tff(c_256, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_250])).
% 3.88/1.65  tff(c_259, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_256])).
% 3.88/1.65  tff(c_14, plain, (![A_5]: (k1_relat_1(k2_funct_1(A_5))=k2_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.88/1.65  tff(c_260, plain, (![B_62, A_63]: (v1_funct_2(B_62, k1_relat_1(B_62), A_63) | ~r1_tarski(k2_relat_1(B_62), A_63) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.88/1.65  tff(c_1125, plain, (![A_127, A_128]: (v1_funct_2(k2_funct_1(A_127), k2_relat_1(A_127), A_128) | ~r1_tarski(k2_relat_1(k2_funct_1(A_127)), A_128) | ~v1_funct_1(k2_funct_1(A_127)) | ~v1_relat_1(k2_funct_1(A_127)) | ~v2_funct_1(A_127) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_14, c_260])).
% 3.88/1.65  tff(c_1128, plain, (![A_128]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_128) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_128) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_1125])).
% 3.88/1.65  tff(c_1134, plain, (![A_129]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_129) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_129))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_207, c_65, c_1128])).
% 3.88/1.65  tff(c_1137, plain, (![A_129]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_129) | ~r1_tarski(k1_relat_1('#skF_3'), A_129) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1134])).
% 3.88/1.65  tff(c_1147, plain, (![A_130]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_130) | ~r1_tarski(k1_relat_1('#skF_3'), A_130))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_38, c_1137])).
% 3.88/1.65  tff(c_190, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 3.88/1.65  tff(c_1150, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1147, c_190])).
% 3.88/1.65  tff(c_1154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_723, c_1150])).
% 3.88/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.65  
% 3.88/1.65  Inference rules
% 3.88/1.65  ----------------------
% 3.88/1.65  #Ref     : 0
% 3.88/1.65  #Sup     : 264
% 3.88/1.65  #Fact    : 0
% 3.88/1.65  #Define  : 0
% 3.88/1.65  #Split   : 6
% 3.88/1.65  #Chain   : 0
% 3.88/1.65  #Close   : 0
% 3.88/1.65  
% 3.88/1.65  Ordering : KBO
% 3.88/1.65  
% 3.88/1.65  Simplification rules
% 3.88/1.65  ----------------------
% 3.88/1.65  #Subsume      : 12
% 3.88/1.65  #Demod        : 222
% 3.88/1.65  #Tautology    : 109
% 3.88/1.65  #SimpNegUnit  : 5
% 3.88/1.65  #BackRed      : 15
% 3.88/1.65  
% 3.88/1.65  #Partial instantiations: 0
% 3.88/1.65  #Strategies tried      : 1
% 3.88/1.65  
% 3.88/1.65  Timing (in seconds)
% 3.88/1.65  ----------------------
% 3.88/1.65  Preprocessing        : 0.32
% 3.88/1.65  Parsing              : 0.17
% 3.88/1.65  CNF conversion       : 0.02
% 3.88/1.65  Main loop            : 0.55
% 3.88/1.65  Inferencing          : 0.21
% 3.88/1.65  Reduction            : 0.18
% 3.88/1.65  Demodulation         : 0.13
% 3.88/1.65  BG Simplification    : 0.02
% 3.88/1.65  Subsumption          : 0.10
% 3.88/1.65  Abstraction          : 0.03
% 3.88/1.65  MUC search           : 0.00
% 3.88/1.65  Cooper               : 0.00
% 3.88/1.65  Total                : 0.92
% 3.88/1.65  Index Insertion      : 0.00
% 3.88/1.66  Index Deletion       : 0.00
% 3.88/1.66  Index Matching       : 0.00
% 3.88/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
