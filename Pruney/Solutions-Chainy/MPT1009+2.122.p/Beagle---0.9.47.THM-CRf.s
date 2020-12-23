%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:59 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 311 expanded)
%              Number of leaves         :   41 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 644 expanded)
%              Number of equality atoms :   36 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_38,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_205,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_208,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_205])).

tff(c_214,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_208])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k9_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_502,plain,(
    ! [B_110,A_111] :
      ( k1_tarski(k1_funct_1(B_110,A_111)) = k2_relat_1(B_110)
      | k1_tarski(A_111) != k1_relat_1(B_110)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_480,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k7_relset_1(A_105,B_106,C_107,D_108) = k9_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_490,plain,(
    ! [D_108] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_108) = k9_relat_1('#skF_4',D_108) ),
    inference(resolution,[status(thm)],[c_60,c_480])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_492,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_56])).

tff(c_508,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_492])).

tff(c_517,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_64,c_508])).

tff(c_586,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_369,plain,(
    ! [C_87,A_88,B_89] :
      ( v4_relat_1(C_87,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_383,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_369])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_351,plain,(
    ! [B_85,A_86] :
      ( k1_tarski(B_85) = A_86
      | k1_xboole_0 = A_86
      | ~ r1_tarski(A_86,k1_tarski(B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_894,plain,(
    ! [B_166,B_167] :
      ( k1_tarski(B_166) = k1_relat_1(B_167)
      | k1_relat_1(B_167) = k1_xboole_0
      | ~ v4_relat_1(B_167,k1_tarski(B_166))
      | ~ v1_relat_1(B_167) ) ),
    inference(resolution,[status(thm)],[c_36,c_351])).

tff(c_920,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_383,c_894])).

tff(c_934,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_920])).

tff(c_935,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_934])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_558,plain,(
    ! [C_118,A_119,B_120] :
      ( m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ r1_tarski(k2_relat_1(C_118),B_120)
      | ~ r1_tarski(k1_relat_1(C_118),A_119)
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1426,plain,(
    ! [C_195,B_196] :
      ( m1_subset_1(C_195,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_195),B_196)
      | ~ r1_tarski(k1_relat_1(C_195),k1_xboole_0)
      | ~ v1_relat_1(C_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_558])).

tff(c_1523,plain,(
    ! [C_202] :
      ( m1_subset_1(C_202,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_202),k1_xboole_0)
      | ~ v1_relat_1(C_202) ) ),
    inference(resolution,[status(thm)],[c_6,c_1426])).

tff(c_1535,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_1523])).

tff(c_1550,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_6,c_1535])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1576,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1550,c_28])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_1603,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1576,c_157])).

tff(c_1646,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_8])).

tff(c_79,plain,(
    ! [A_41] : k2_zfmisc_1(A_41,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_38])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_171,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k9_relat_1(B_55,A_56),k2_relat_1(B_55))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_176,plain,(
    ! [A_56] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_56),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_171])).

tff(c_180,plain,(
    ! [A_57] : r1_tarski(k9_relat_1(k1_xboole_0,A_57),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_176])).

tff(c_186,plain,(
    ! [A_57] : k9_relat_1(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_157])).

tff(c_1640,plain,(
    ! [A_57] : k9_relat_1('#skF_4',A_57) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_1603,c_186])).

tff(c_1897,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_492])).

tff(c_1901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_1897])).

tff(c_1902,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_1927,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1902])).

tff(c_1931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.61  
% 3.85/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.61  
% 3.85/1.61  %Foreground sorts:
% 3.85/1.61  
% 3.85/1.61  
% 3.85/1.61  %Background operators:
% 3.85/1.61  
% 3.85/1.61  
% 3.85/1.61  %Foreground operators:
% 3.85/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.85/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.85/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.85/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.85/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.85/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.85/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.62  
% 3.85/1.63  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.85/1.63  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.85/1.63  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.85/1.63  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.85/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.85/1.63  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.85/1.63  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.85/1.63  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.85/1.63  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.85/1.63  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.85/1.63  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.85/1.63  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.85/1.63  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.85/1.63  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.63  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.85/1.63  tff(c_38, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.85/1.63  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.85/1.63  tff(c_205, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.63  tff(c_208, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_205])).
% 3.85/1.63  tff(c_214, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_208])).
% 3.85/1.63  tff(c_40, plain, (![B_24, A_23]: (r1_tarski(k9_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.85/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.63  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.85/1.63  tff(c_502, plain, (![B_110, A_111]: (k1_tarski(k1_funct_1(B_110, A_111))=k2_relat_1(B_110) | k1_tarski(A_111)!=k1_relat_1(B_110) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.85/1.63  tff(c_480, plain, (![A_105, B_106, C_107, D_108]: (k7_relset_1(A_105, B_106, C_107, D_108)=k9_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.85/1.63  tff(c_490, plain, (![D_108]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_108)=k9_relat_1('#skF_4', D_108))), inference(resolution, [status(thm)], [c_60, c_480])).
% 3.85/1.63  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.85/1.63  tff(c_492, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_56])).
% 3.85/1.63  tff(c_508, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_502, c_492])).
% 3.85/1.63  tff(c_517, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_64, c_508])).
% 3.85/1.63  tff(c_586, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_517])).
% 3.85/1.63  tff(c_369, plain, (![C_87, A_88, B_89]: (v4_relat_1(C_87, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.85/1.63  tff(c_383, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_369])).
% 3.85/1.63  tff(c_36, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.63  tff(c_351, plain, (![B_85, A_86]: (k1_tarski(B_85)=A_86 | k1_xboole_0=A_86 | ~r1_tarski(A_86, k1_tarski(B_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.85/1.63  tff(c_894, plain, (![B_166, B_167]: (k1_tarski(B_166)=k1_relat_1(B_167) | k1_relat_1(B_167)=k1_xboole_0 | ~v4_relat_1(B_167, k1_tarski(B_166)) | ~v1_relat_1(B_167))), inference(resolution, [status(thm)], [c_36, c_351])).
% 3.85/1.63  tff(c_920, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_383, c_894])).
% 3.85/1.63  tff(c_934, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_214, c_920])).
% 3.85/1.63  tff(c_935, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_586, c_934])).
% 3.85/1.63  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.85/1.63  tff(c_558, plain, (![C_118, A_119, B_120]: (m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~r1_tarski(k2_relat_1(C_118), B_120) | ~r1_tarski(k1_relat_1(C_118), A_119) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.63  tff(c_1426, plain, (![C_195, B_196]: (m1_subset_1(C_195, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_195), B_196) | ~r1_tarski(k1_relat_1(C_195), k1_xboole_0) | ~v1_relat_1(C_195))), inference(superposition, [status(thm), theory('equality')], [c_26, c_558])).
% 3.85/1.63  tff(c_1523, plain, (![C_202]: (m1_subset_1(C_202, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_202), k1_xboole_0) | ~v1_relat_1(C_202))), inference(resolution, [status(thm)], [c_6, c_1426])).
% 3.85/1.63  tff(c_1535, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_935, c_1523])).
% 3.85/1.63  tff(c_1550, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_6, c_1535])).
% 3.85/1.63  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.85/1.63  tff(c_1576, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_1550, c_28])).
% 3.85/1.63  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.63  tff(c_145, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.63  tff(c_157, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_145])).
% 3.85/1.63  tff(c_1603, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1576, c_157])).
% 3.85/1.63  tff(c_1646, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_8])).
% 3.85/1.63  tff(c_79, plain, (![A_41]: (k2_zfmisc_1(A_41, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.85/1.63  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_38])).
% 3.85/1.63  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.63  tff(c_171, plain, (![B_55, A_56]: (r1_tarski(k9_relat_1(B_55, A_56), k2_relat_1(B_55)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.85/1.63  tff(c_176, plain, (![A_56]: (r1_tarski(k9_relat_1(k1_xboole_0, A_56), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_171])).
% 3.85/1.63  tff(c_180, plain, (![A_57]: (r1_tarski(k9_relat_1(k1_xboole_0, A_57), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_176])).
% 3.85/1.63  tff(c_186, plain, (![A_57]: (k9_relat_1(k1_xboole_0, A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_180, c_157])).
% 3.85/1.63  tff(c_1640, plain, (![A_57]: (k9_relat_1('#skF_4', A_57)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_1603, c_186])).
% 3.85/1.63  tff(c_1897, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_492])).
% 3.85/1.63  tff(c_1901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1646, c_1897])).
% 3.85/1.63  tff(c_1902, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_517])).
% 3.85/1.63  tff(c_1927, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1902])).
% 3.85/1.63  tff(c_1931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_1927])).
% 3.85/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.63  
% 3.85/1.63  Inference rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Ref     : 0
% 3.85/1.63  #Sup     : 396
% 3.85/1.63  #Fact    : 1
% 3.85/1.63  #Define  : 0
% 3.85/1.63  #Split   : 4
% 3.85/1.63  #Chain   : 0
% 3.85/1.63  #Close   : 0
% 3.85/1.63  
% 3.85/1.63  Ordering : KBO
% 3.85/1.63  
% 3.85/1.63  Simplification rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Subsume      : 53
% 3.85/1.63  #Demod        : 482
% 3.85/1.63  #Tautology    : 218
% 3.85/1.63  #SimpNegUnit  : 10
% 3.85/1.63  #BackRed      : 58
% 3.85/1.63  
% 3.85/1.63  #Partial instantiations: 0
% 3.85/1.63  #Strategies tried      : 1
% 3.85/1.63  
% 3.85/1.63  Timing (in seconds)
% 3.85/1.63  ----------------------
% 3.85/1.63  Preprocessing        : 0.34
% 3.85/1.63  Parsing              : 0.18
% 3.85/1.63  CNF conversion       : 0.02
% 3.85/1.63  Main loop            : 0.53
% 3.85/1.63  Inferencing          : 0.18
% 3.85/1.63  Reduction            : 0.19
% 3.85/1.63  Demodulation         : 0.14
% 3.85/1.63  BG Simplification    : 0.02
% 3.85/1.63  Subsumption          : 0.10
% 3.85/1.63  Abstraction          : 0.02
% 3.85/1.63  MUC search           : 0.00
% 3.85/1.63  Cooper               : 0.00
% 3.85/1.63  Total                : 0.90
% 3.85/1.63  Index Insertion      : 0.00
% 3.85/1.63  Index Deletion       : 0.00
% 3.85/1.63  Index Matching       : 0.00
% 3.85/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
