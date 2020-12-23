%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:04 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 628 expanded)
%              Number of leaves         :   42 ( 234 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 (1111 expanded)
%              Number of equality atoms :   47 ( 360 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_51,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

tff(c_40,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_59,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_134,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_136,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_51,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_59,c_134])).

tff(c_143,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_143])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_157,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_12])).

tff(c_273,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k8_relset_1(A_73,B_74,C_75,D_76) = k10_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_281,plain,(
    ! [A_73,B_74,D_76] : k8_relset_1(A_73,B_74,'#skF_4',D_76) = k10_relat_1('#skF_4',D_76) ),
    inference(resolution,[status(thm)],[c_157,c_273])).

tff(c_355,plain,(
    ! [A_98,B_99,C_100] :
      ( k8_relset_1(A_98,B_99,C_100,B_99) = k1_relset_1(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_364,plain,(
    ! [A_98,B_99] : k8_relset_1(A_98,B_99,'#skF_4',B_99) = k1_relset_1(A_98,B_99,'#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_355])).

tff(c_367,plain,(
    ! [A_98,B_99] : k1_relset_1(A_98,B_99,'#skF_4') = k10_relat_1('#skF_4',B_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_364])).

tff(c_18,plain,(
    ! [A_11] : k9_relat_1(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_160,plain,(
    ! [A_11] : k9_relat_1('#skF_4',A_11) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_18])).

tff(c_263,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k7_relset_1(A_69,B_70,C_71,D_72) = k9_relat_1(C_71,D_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_270,plain,(
    ! [A_69,B_70,D_72] : k7_relset_1(A_69,B_70,'#skF_4',D_72) = k9_relat_1('#skF_4',D_72) ),
    inference(resolution,[status(thm)],[c_157,c_263])).

tff(c_272,plain,(
    ! [A_69,B_70,D_72] : k7_relset_1(A_69,B_70,'#skF_4',D_72) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_270])).

tff(c_470,plain,(
    ! [B_131,A_132,C_133] :
      ( k8_relset_1(B_131,A_132,C_133,k7_relset_1(B_131,A_132,C_133,B_131)) = k1_relset_1(B_131,A_132,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(B_131,A_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_479,plain,(
    ! [B_131,A_132] : k8_relset_1(B_131,A_132,'#skF_4',k7_relset_1(B_131,A_132,'#skF_4',B_131)) = k1_relset_1(B_131,A_132,'#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_470])).

tff(c_482,plain,(
    ! [A_132] : k10_relat_1('#skF_4',A_132) = k10_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_281,c_272,c_479])).

tff(c_52,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_154,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_52])).

tff(c_289,plain,(
    k10_relat_1('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_154])).

tff(c_483,plain,(
    k10_relat_1('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_289])).

tff(c_491,plain,(
    ! [A_132] : k10_relat_1('#skF_4',A_132) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_483])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_113,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    ! [C_48] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_113])).

tff(c_131,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_123])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_162,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_4])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_161,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_20])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_163,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_22])).

tff(c_236,plain,(
    ! [B_62,A_63] :
      ( v1_funct_2(B_62,k1_relat_1(B_62),A_63)
      | ~ r1_tarski(k2_relat_1(B_62),A_63)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_239,plain,(
    ! [A_63] :
      ( v1_funct_2('#skF_4','#skF_4',A_63)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_63)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_236])).

tff(c_241,plain,(
    ! [A_63] : v1_funct_2('#skF_4','#skF_4',A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_58,c_162,c_161,c_239])).

tff(c_48,plain,(
    ! [B_34,C_35] :
      ( k8_relset_1(k1_xboole_0,B_34,C_35,k7_relset_1(k1_xboole_0,B_34,C_35,k1_xboole_0)) = k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34)))
      | ~ v1_funct_2(C_35,k1_xboole_0,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    ! [B_34,C_35] :
      ( k8_relset_1(k1_xboole_0,B_34,C_35,k7_relset_1(k1_xboole_0,B_34,C_35,k1_xboole_0)) = k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(C_35,k1_xboole_0,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_519,plain,(
    ! [B_138,C_139] :
      ( k8_relset_1('#skF_4',B_138,C_139,k7_relset_1('#skF_4',B_138,C_139,'#skF_4')) = '#skF_4'
      | ~ m1_subset_1(C_139,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(C_139,'#skF_4',B_138)
      | ~ v1_funct_1(C_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_148,c_148,c_148,c_148,c_60])).

tff(c_522,plain,(
    ! [B_138] :
      ( k8_relset_1('#skF_4',B_138,'#skF_4',k7_relset_1('#skF_4',B_138,'#skF_4','#skF_4')) = '#skF_4'
      | ~ v1_funct_2('#skF_4','#skF_4',B_138)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_157,c_519])).

tff(c_525,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_241,c_281,c_272,c_522])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.83/1.40  
% 2.83/1.40  %Foreground sorts:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Background operators:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Foreground operators:
% 2.83/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.83/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.83/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.40  
% 2.83/1.42  tff(f_88, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.83/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.83/1.42  tff(f_34, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.83/1.42  tff(f_121, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.83/1.42  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.83/1.42  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.83/1.42  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.83/1.42  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.83/1.42  tff(f_51, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.83/1.42  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.83/1.42  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.83/1.42  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.42  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.83/1.42  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.83/1.42  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.83/1.42  tff(f_112, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_2)).
% 2.83/1.42  tff(c_40, plain, (![A_29]: (r2_hidden('#skF_1'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.83/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.83/1.42  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.83/1.42  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.83/1.42  tff(c_59, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_54])).
% 2.83/1.42  tff(c_134, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.42  tff(c_136, plain, (![A_51]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_51, '#skF_4'))), inference(resolution, [status(thm)], [c_59, c_134])).
% 2.83/1.42  tff(c_143, plain, (![A_52]: (~r2_hidden(A_52, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_136])).
% 2.83/1.42  tff(c_148, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_143])).
% 2.83/1.42  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.42  tff(c_157, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_12])).
% 2.83/1.42  tff(c_273, plain, (![A_73, B_74, C_75, D_76]: (k8_relset_1(A_73, B_74, C_75, D_76)=k10_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.42  tff(c_281, plain, (![A_73, B_74, D_76]: (k8_relset_1(A_73, B_74, '#skF_4', D_76)=k10_relat_1('#skF_4', D_76))), inference(resolution, [status(thm)], [c_157, c_273])).
% 2.83/1.42  tff(c_355, plain, (![A_98, B_99, C_100]: (k8_relset_1(A_98, B_99, C_100, B_99)=k1_relset_1(A_98, B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.42  tff(c_364, plain, (![A_98, B_99]: (k8_relset_1(A_98, B_99, '#skF_4', B_99)=k1_relset_1(A_98, B_99, '#skF_4'))), inference(resolution, [status(thm)], [c_157, c_355])).
% 2.83/1.42  tff(c_367, plain, (![A_98, B_99]: (k1_relset_1(A_98, B_99, '#skF_4')=k10_relat_1('#skF_4', B_99))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_364])).
% 2.83/1.42  tff(c_18, plain, (![A_11]: (k9_relat_1(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.42  tff(c_160, plain, (![A_11]: (k9_relat_1('#skF_4', A_11)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_18])).
% 2.83/1.42  tff(c_263, plain, (![A_69, B_70, C_71, D_72]: (k7_relset_1(A_69, B_70, C_71, D_72)=k9_relat_1(C_71, D_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.42  tff(c_270, plain, (![A_69, B_70, D_72]: (k7_relset_1(A_69, B_70, '#skF_4', D_72)=k9_relat_1('#skF_4', D_72))), inference(resolution, [status(thm)], [c_157, c_263])).
% 2.83/1.42  tff(c_272, plain, (![A_69, B_70, D_72]: (k7_relset_1(A_69, B_70, '#skF_4', D_72)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_270])).
% 2.83/1.42  tff(c_470, plain, (![B_131, A_132, C_133]: (k8_relset_1(B_131, A_132, C_133, k7_relset_1(B_131, A_132, C_133, B_131))=k1_relset_1(B_131, A_132, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(B_131, A_132))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.42  tff(c_479, plain, (![B_131, A_132]: (k8_relset_1(B_131, A_132, '#skF_4', k7_relset_1(B_131, A_132, '#skF_4', B_131))=k1_relset_1(B_131, A_132, '#skF_4'))), inference(resolution, [status(thm)], [c_157, c_470])).
% 2.83/1.42  tff(c_482, plain, (![A_132]: (k10_relat_1('#skF_4', A_132)=k10_relat_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_281, c_272, c_479])).
% 2.83/1.42  tff(c_52, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.83/1.42  tff(c_154, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_52])).
% 2.83/1.42  tff(c_289, plain, (k10_relat_1('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_154])).
% 2.83/1.42  tff(c_483, plain, (k10_relat_1('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_289])).
% 2.83/1.42  tff(c_491, plain, (![A_132]: (k10_relat_1('#skF_4', A_132)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_482, c_483])).
% 2.83/1.42  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.83/1.42  tff(c_113, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.42  tff(c_123, plain, (![C_48]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_113])).
% 2.83/1.42  tff(c_131, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_59, c_123])).
% 2.83/1.42  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.83/1.42  tff(c_162, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_4])).
% 2.83/1.42  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.83/1.42  tff(c_161, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_20])).
% 2.83/1.42  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.83/1.42  tff(c_163, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_22])).
% 2.83/1.42  tff(c_236, plain, (![B_62, A_63]: (v1_funct_2(B_62, k1_relat_1(B_62), A_63) | ~r1_tarski(k2_relat_1(B_62), A_63) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.83/1.42  tff(c_239, plain, (![A_63]: (v1_funct_2('#skF_4', '#skF_4', A_63) | ~r1_tarski(k2_relat_1('#skF_4'), A_63) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_236])).
% 2.83/1.42  tff(c_241, plain, (![A_63]: (v1_funct_2('#skF_4', '#skF_4', A_63))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_58, c_162, c_161, c_239])).
% 2.83/1.42  tff(c_48, plain, (![B_34, C_35]: (k8_relset_1(k1_xboole_0, B_34, C_35, k7_relset_1(k1_xboole_0, B_34, C_35, k1_xboole_0))=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))) | ~v1_funct_2(C_35, k1_xboole_0, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.83/1.42  tff(c_60, plain, (![B_34, C_35]: (k8_relset_1(k1_xboole_0, B_34, C_35, k7_relset_1(k1_xboole_0, B_34, C_35, k1_xboole_0))=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(C_35, k1_xboole_0, B_34) | ~v1_funct_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 2.83/1.42  tff(c_519, plain, (![B_138, C_139]: (k8_relset_1('#skF_4', B_138, C_139, k7_relset_1('#skF_4', B_138, C_139, '#skF_4'))='#skF_4' | ~m1_subset_1(C_139, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(C_139, '#skF_4', B_138) | ~v1_funct_1(C_139))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_148, c_148, c_148, c_148, c_60])).
% 2.83/1.42  tff(c_522, plain, (![B_138]: (k8_relset_1('#skF_4', B_138, '#skF_4', k7_relset_1('#skF_4', B_138, '#skF_4', '#skF_4'))='#skF_4' | ~v1_funct_2('#skF_4', '#skF_4', B_138) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_157, c_519])).
% 2.83/1.42  tff(c_525, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_241, c_281, c_272, c_522])).
% 2.83/1.42  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_525])).
% 2.83/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  Inference rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Ref     : 0
% 2.83/1.42  #Sup     : 117
% 2.83/1.42  #Fact    : 0
% 2.83/1.42  #Define  : 0
% 2.83/1.42  #Split   : 0
% 2.83/1.42  #Chain   : 0
% 2.83/1.42  #Close   : 0
% 2.83/1.42  
% 2.83/1.42  Ordering : KBO
% 2.83/1.42  
% 2.83/1.42  Simplification rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Subsume      : 26
% 2.83/1.42  #Demod        : 103
% 2.83/1.42  #Tautology    : 60
% 2.83/1.42  #SimpNegUnit  : 1
% 2.83/1.42  #BackRed      : 18
% 2.83/1.42  
% 2.83/1.42  #Partial instantiations: 0
% 2.83/1.42  #Strategies tried      : 1
% 2.83/1.42  
% 2.83/1.42  Timing (in seconds)
% 2.83/1.42  ----------------------
% 2.83/1.42  Preprocessing        : 0.35
% 2.83/1.42  Parsing              : 0.18
% 2.83/1.42  CNF conversion       : 0.02
% 2.83/1.42  Main loop            : 0.29
% 2.83/1.42  Inferencing          : 0.10
% 2.83/1.42  Reduction            : 0.10
% 2.83/1.42  Demodulation         : 0.07
% 2.83/1.42  BG Simplification    : 0.02
% 2.83/1.42  Subsumption          : 0.04
% 2.83/1.42  Abstraction          : 0.02
% 2.83/1.42  MUC search           : 0.00
% 2.83/1.42  Cooper               : 0.00
% 2.83/1.42  Total                : 0.67
% 2.83/1.42  Index Insertion      : 0.00
% 2.83/1.42  Index Deletion       : 0.00
% 2.83/1.42  Index Matching       : 0.00
% 2.83/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
