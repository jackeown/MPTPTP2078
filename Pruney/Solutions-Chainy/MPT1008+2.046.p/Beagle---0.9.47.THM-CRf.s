%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 194 expanded)
%              Number of leaves         :   41 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 393 expanded)
%              Number of equality atoms :   55 ( 160 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_14,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_106,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_106])).

tff(c_32,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_118,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_32])).

tff(c_120,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_193,plain,(
    ! [B_71,A_72] :
      ( k1_tarski(k1_funct_1(B_71,A_72)) = k2_relat_1(B_71)
      | k1_tarski(A_72) != k1_relat_1(B_71)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_178,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_182,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_178])).

tff(c_48,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_183,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_48])).

tff(c_199,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_183])).

tff(c_217,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_56,c_199])).

tff(c_126,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_130,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,(
    ! [B_60,A_61] :
      ( k1_tarski(B_60) = A_61
      | k1_xboole_0 = A_61
      | ~ r1_tarski(A_61,k1_tarski(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_224,plain,(
    ! [B_75,B_76] :
      ( k1_tarski(B_75) = k1_relat_1(B_76)
      | k1_relat_1(B_76) = k1_xboole_0
      | ~ v4_relat_1(B_76,k1_tarski(B_75))
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_230,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_224])).

tff(c_233,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_230])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_217,c_233])).

tff(c_236,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_244,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_236,c_26])).

tff(c_30,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_30])).

tff(c_119,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_238,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_119])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_238])).

tff(c_273,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_278,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_6])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_281,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_50])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_274,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_302,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_274])).

tff(c_394,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_397,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_394])).

tff(c_399,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_397])).

tff(c_46,plain,(
    ! [D_34,C_33,A_31,B_32] :
      ( r2_hidden(k1_funct_1(D_34,C_33),k2_relset_1(A_31,B_32,D_34))
      | k1_xboole_0 = B_32
      | ~ r2_hidden(C_33,A_31)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(D_34,A_31,B_32)
      | ~ v1_funct_1(D_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_496,plain,(
    ! [D_120,C_121,A_122,B_123] :
      ( r2_hidden(k1_funct_1(D_120,C_121),k2_relset_1(A_122,B_123,D_120))
      | B_123 = '#skF_4'
      | ~ r2_hidden(C_121,A_122)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_2(D_120,A_122,B_123)
      | ~ v1_funct_1(D_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_46])).

tff(c_505,plain,(
    ! [C_121] :
      ( r2_hidden(k1_funct_1('#skF_4',C_121),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_121,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_496])).

tff(c_509,plain,(
    ! [C_121] :
      ( r2_hidden(k1_funct_1('#skF_4',C_121),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_121,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_505])).

tff(c_511,plain,(
    ! [C_124] :
      ( r2_hidden(k1_funct_1('#skF_4',C_124),'#skF_4')
      | ~ r2_hidden(C_124,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_509])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_514,plain,(
    ! [C_124] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_124))
      | ~ r2_hidden(C_124,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_511,c_36])).

tff(c_524,plain,(
    ! [C_125] : ~ r2_hidden(C_125,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_514])).

tff(c_528,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_524])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.65  
% 2.78/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.78/1.66  
% 2.78/1.66  %Foreground sorts:
% 2.78/1.66  
% 2.78/1.66  
% 2.78/1.66  %Background operators:
% 2.78/1.66  
% 2.78/1.66  
% 2.78/1.66  %Foreground operators:
% 2.78/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.66  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.78/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.66  
% 2.98/1.67  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.98/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.98/1.67  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.98/1.67  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.98/1.67  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.98/1.67  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.98/1.67  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.98/1.67  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.98/1.67  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.98/1.67  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.98/1.67  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.98/1.67  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.98/1.67  tff(f_104, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.98/1.67  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.98/1.67  tff(c_14, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.98/1.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.67  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.98/1.67  tff(c_106, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.98/1.67  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_106])).
% 2.98/1.67  tff(c_32, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.98/1.67  tff(c_118, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_110, c_32])).
% 2.98/1.67  tff(c_120, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_118])).
% 2.98/1.67  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.98/1.67  tff(c_193, plain, (![B_71, A_72]: (k1_tarski(k1_funct_1(B_71, A_72))=k2_relat_1(B_71) | k1_tarski(A_72)!=k1_relat_1(B_71) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.67  tff(c_178, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.98/1.67  tff(c_182, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_178])).
% 2.98/1.67  tff(c_48, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.98/1.67  tff(c_183, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_48])).
% 2.98/1.67  tff(c_199, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_193, c_183])).
% 2.98/1.67  tff(c_217, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_56, c_199])).
% 2.98/1.67  tff(c_126, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.98/1.67  tff(c_130, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_126])).
% 2.98/1.67  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.98/1.67  tff(c_141, plain, (![B_60, A_61]: (k1_tarski(B_60)=A_61 | k1_xboole_0=A_61 | ~r1_tarski(A_61, k1_tarski(B_60)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.98/1.67  tff(c_224, plain, (![B_75, B_76]: (k1_tarski(B_75)=k1_relat_1(B_76) | k1_relat_1(B_76)=k1_xboole_0 | ~v4_relat_1(B_76, k1_tarski(B_75)) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_24, c_141])).
% 2.98/1.67  tff(c_230, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_130, c_224])).
% 2.98/1.67  tff(c_233, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_230])).
% 2.98/1.67  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_217, c_233])).
% 2.98/1.67  tff(c_236, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_118])).
% 2.98/1.67  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.67  tff(c_244, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_236, c_26])).
% 2.98/1.67  tff(c_30, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.98/1.67  tff(c_117, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_110, c_30])).
% 2.98/1.67  tff(c_119, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_117])).
% 2.98/1.67  tff(c_238, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_119])).
% 2.98/1.67  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_238])).
% 2.98/1.67  tff(c_273, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_117])).
% 2.98/1.67  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.67  tff(c_278, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_6])).
% 2.98/1.67  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.98/1.67  tff(c_281, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_50])).
% 2.98/1.67  tff(c_54, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.98/1.67  tff(c_274, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_117])).
% 2.98/1.67  tff(c_302, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_274])).
% 2.98/1.67  tff(c_394, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.98/1.67  tff(c_397, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_394])).
% 2.98/1.67  tff(c_399, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_302, c_397])).
% 2.98/1.67  tff(c_46, plain, (![D_34, C_33, A_31, B_32]: (r2_hidden(k1_funct_1(D_34, C_33), k2_relset_1(A_31, B_32, D_34)) | k1_xboole_0=B_32 | ~r2_hidden(C_33, A_31) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(D_34, A_31, B_32) | ~v1_funct_1(D_34))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.98/1.67  tff(c_496, plain, (![D_120, C_121, A_122, B_123]: (r2_hidden(k1_funct_1(D_120, C_121), k2_relset_1(A_122, B_123, D_120)) | B_123='#skF_4' | ~r2_hidden(C_121, A_122) | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_2(D_120, A_122, B_123) | ~v1_funct_1(D_120))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_46])).
% 2.98/1.67  tff(c_505, plain, (![C_121]: (r2_hidden(k1_funct_1('#skF_4', C_121), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_121, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_496])).
% 2.98/1.67  tff(c_509, plain, (![C_121]: (r2_hidden(k1_funct_1('#skF_4', C_121), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_121, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_505])).
% 2.98/1.67  tff(c_511, plain, (![C_124]: (r2_hidden(k1_funct_1('#skF_4', C_124), '#skF_4') | ~r2_hidden(C_124, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_281, c_509])).
% 2.98/1.67  tff(c_36, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.98/1.67  tff(c_514, plain, (![C_124]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_124)) | ~r2_hidden(C_124, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_511, c_36])).
% 2.98/1.67  tff(c_524, plain, (![C_125]: (~r2_hidden(C_125, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_514])).
% 2.98/1.67  tff(c_528, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_524])).
% 2.98/1.67  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_528])).
% 2.98/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.67  
% 2.98/1.67  Inference rules
% 2.98/1.67  ----------------------
% 2.98/1.67  #Ref     : 0
% 2.98/1.67  #Sup     : 99
% 2.98/1.67  #Fact    : 0
% 2.98/1.67  #Define  : 0
% 2.98/1.67  #Split   : 3
% 2.98/1.67  #Chain   : 0
% 2.98/1.67  #Close   : 0
% 2.98/1.67  
% 2.98/1.67  Ordering : KBO
% 2.98/1.67  
% 2.98/1.67  Simplification rules
% 2.98/1.67  ----------------------
% 2.98/1.67  #Subsume      : 9
% 2.98/1.67  #Demod        : 89
% 2.98/1.67  #Tautology    : 54
% 2.98/1.67  #SimpNegUnit  : 6
% 2.98/1.67  #BackRed      : 17
% 2.98/1.67  
% 2.98/1.67  #Partial instantiations: 0
% 2.98/1.67  #Strategies tried      : 1
% 2.98/1.67  
% 2.98/1.67  Timing (in seconds)
% 2.98/1.67  ----------------------
% 2.98/1.67  Preprocessing        : 0.46
% 2.98/1.67  Parsing              : 0.27
% 2.98/1.67  CNF conversion       : 0.03
% 2.98/1.67  Main loop            : 0.29
% 2.98/1.67  Inferencing          : 0.10
% 2.98/1.67  Reduction            : 0.09
% 2.98/1.68  Demodulation         : 0.06
% 2.98/1.68  BG Simplification    : 0.02
% 2.98/1.68  Subsumption          : 0.05
% 2.98/1.68  Abstraction          : 0.01
% 2.98/1.68  MUC search           : 0.00
% 2.98/1.68  Cooper               : 0.00
% 2.98/1.68  Total                : 0.79
% 2.98/1.68  Index Insertion      : 0.00
% 2.98/1.68  Index Deletion       : 0.00
% 2.98/1.68  Index Matching       : 0.00
% 2.98/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
