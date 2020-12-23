%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:57 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 133 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 300 expanded)
%              Number of equality atoms :   36 ( 110 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_308,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k8_relset_1(A_76,B_77,C_78,D_79) = k10_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_319,plain,(
    ! [D_79] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_79) = k10_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_44,c_308])).

tff(c_159,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_174,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_417,plain,(
    ! [A_102,B_103,C_104] :
      ( k8_relset_1(A_102,B_103,C_104,B_103) = k1_relset_1(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_422,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_417])).

tff(c_429,plain,(
    k10_relat_1('#skF_4','#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_174,c_422])).

tff(c_488,plain,(
    ! [B_120,A_121,C_122] :
      ( k1_xboole_0 = B_120
      | k8_relset_1(A_121,B_120,C_122,B_120) = A_121
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120)))
      | ~ v1_funct_2(C_122,A_121,B_120)
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_493,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_488])).

tff(c_501,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_429,c_319,c_493])).

tff(c_502,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_501])).

tff(c_97,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_97])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k10_relat_1(B_9,k9_relat_1(B_9,A_8)))
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_248,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k7_relset_1(A_67,B_68,C_69,D_70) = k9_relat_1(C_69,D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_259,plain,(
    ! [D_70] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_70) = k9_relat_1('#skF_4',D_70) ),
    inference(resolution,[status(thm)],[c_44,c_248])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_276,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_38])).

tff(c_329,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_276])).

tff(c_341,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_329])).

tff(c_344,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_341])).

tff(c_505,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_344])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_505])).

tff(c_510,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_513,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_8])).

tff(c_560,plain,(
    ! [B_130,A_131] :
      ( B_130 = A_131
      | ~ r1_tarski(B_130,A_131)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_568,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_560])).

tff(c_579,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_568])).

tff(c_511,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_518,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_511])).

tff(c_554,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_518,c_38])).

tff(c_580,plain,(
    ~ r1_tarski('#skF_1',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_554])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:51:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.34  
% 2.37/1.34  %Foreground sorts:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Background operators:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Foreground operators:
% 2.37/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.37/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.37/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.34  
% 2.65/1.36  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_2)).
% 2.65/1.36  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.65/1.36  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.65/1.36  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.65/1.36  tff(f_83, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 2.65/1.36  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.65/1.36  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.65/1.36  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.65/1.36  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.36  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.36  tff(c_40, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.36  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 2.65/1.36  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.36  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.36  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.36  tff(c_308, plain, (![A_76, B_77, C_78, D_79]: (k8_relset_1(A_76, B_77, C_78, D_79)=k10_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.36  tff(c_319, plain, (![D_79]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_79)=k10_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_44, c_308])).
% 2.65/1.36  tff(c_159, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.36  tff(c_174, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_159])).
% 2.65/1.36  tff(c_417, plain, (![A_102, B_103, C_104]: (k8_relset_1(A_102, B_103, C_104, B_103)=k1_relset_1(A_102, B_103, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.36  tff(c_422, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_417])).
% 2.65/1.36  tff(c_429, plain, (k10_relat_1('#skF_4', '#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_174, c_422])).
% 2.65/1.36  tff(c_488, plain, (![B_120, A_121, C_122]: (k1_xboole_0=B_120 | k8_relset_1(A_121, B_120, C_122, B_120)=A_121 | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))) | ~v1_funct_2(C_122, A_121, B_120) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.65/1.36  tff(c_493, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_488])).
% 2.65/1.36  tff(c_501, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_429, c_319, c_493])).
% 2.65/1.36  tff(c_502, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_501])).
% 2.65/1.36  tff(c_97, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.36  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_97])).
% 2.65/1.36  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, k10_relat_1(B_9, k9_relat_1(B_9, A_8))) | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.36  tff(c_248, plain, (![A_67, B_68, C_69, D_70]: (k7_relset_1(A_67, B_68, C_69, D_70)=k9_relat_1(C_69, D_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.36  tff(c_259, plain, (![D_70]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_70)=k9_relat_1('#skF_4', D_70))), inference(resolution, [status(thm)], [c_44, c_248])).
% 2.65/1.36  tff(c_38, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.36  tff(c_276, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_38])).
% 2.65/1.36  tff(c_329, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_276])).
% 2.65/1.36  tff(c_341, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_329])).
% 2.65/1.36  tff(c_344, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_341])).
% 2.65/1.36  tff(c_505, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_344])).
% 2.65/1.36  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_505])).
% 2.65/1.36  tff(c_510, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 2.65/1.36  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.36  tff(c_513, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_8])).
% 2.65/1.36  tff(c_560, plain, (![B_130, A_131]: (B_130=A_131 | ~r1_tarski(B_130, A_131) | ~r1_tarski(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.36  tff(c_568, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_560])).
% 2.65/1.36  tff(c_579, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_568])).
% 2.65/1.36  tff(c_511, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 2.65/1.36  tff(c_518, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_511])).
% 2.65/1.36  tff(c_554, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_518, c_38])).
% 2.65/1.36  tff(c_580, plain, (~r1_tarski('#skF_1', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_554])).
% 2.65/1.36  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_513, c_580])).
% 2.65/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  Inference rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Ref     : 0
% 2.65/1.36  #Sup     : 124
% 2.65/1.36  #Fact    : 0
% 2.65/1.36  #Define  : 0
% 2.65/1.36  #Split   : 3
% 2.65/1.36  #Chain   : 0
% 2.65/1.36  #Close   : 0
% 2.65/1.36  
% 2.65/1.36  Ordering : KBO
% 2.65/1.36  
% 2.65/1.36  Simplification rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Subsume      : 6
% 2.65/1.36  #Demod        : 52
% 2.65/1.36  #Tautology    : 69
% 2.65/1.36  #SimpNegUnit  : 1
% 2.65/1.36  #BackRed      : 10
% 2.65/1.36  
% 2.65/1.36  #Partial instantiations: 0
% 2.65/1.36  #Strategies tried      : 1
% 2.65/1.36  
% 2.65/1.36  Timing (in seconds)
% 2.65/1.36  ----------------------
% 2.65/1.36  Preprocessing        : 0.32
% 2.65/1.36  Parsing              : 0.17
% 2.65/1.36  CNF conversion       : 0.02
% 2.65/1.36  Main loop            : 0.29
% 2.65/1.36  Inferencing          : 0.10
% 2.65/1.36  Reduction            : 0.09
% 2.65/1.36  Demodulation         : 0.07
% 2.65/1.36  BG Simplification    : 0.02
% 2.65/1.36  Subsumption          : 0.05
% 2.65/1.36  Abstraction          : 0.01
% 2.65/1.36  MUC search           : 0.00
% 2.65/1.36  Cooper               : 0.00
% 2.65/1.36  Total                : 0.64
% 2.65/1.36  Index Insertion      : 0.00
% 2.65/1.36  Index Deletion       : 0.00
% 2.65/1.37  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
