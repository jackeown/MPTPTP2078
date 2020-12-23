%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:14 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 131 expanded)
%              Number of leaves         :   38 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 252 expanded)
%              Number of equality atoms :   37 (  61 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_513,plain,(
    ! [B_118,C_119,A_120] :
      ( r2_hidden(B_118,C_119)
      | ~ r1_tarski(k2_tarski(A_120,B_118),C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_527,plain,(
    ! [B_121,A_122] : r2_hidden(B_121,k2_tarski(A_122,B_121)) ),
    inference(resolution,[status(thm)],[c_6,c_513])).

tff(c_533,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_527])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_81,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_192,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_196,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_192])).

tff(c_291,plain,(
    ! [B_94,C_95,A_96] :
      ( r2_hidden(k1_funct_1(B_94,C_95),A_96)
      | ~ r2_hidden(C_95,k1_relat_1(B_94))
      | ~ v1_funct_1(B_94)
      | ~ v5_relat_1(B_94,A_96)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_300,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_291,c_48])).

tff(c_305,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_196,c_56,c_300])).

tff(c_109,plain,(
    ! [A_47] :
      ( k1_relat_1(A_47) = k1_xboole_0
      | k2_relat_1(A_47) != k1_xboole_0
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_113,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_109])).

tff(c_119,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_114,plain,(
    ! [A_48] :
      ( k2_relat_1(A_48) = k1_xboole_0
      | k1_relat_1(A_48) != k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_114])).

tff(c_120,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_118])).

tff(c_186,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_190,plain,(
    v4_relat_1('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_186])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(B_76) = A_77
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,k1_tarski(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_435,plain,(
    ! [B_116,B_117] :
      ( k1_tarski(B_116) = k1_relat_1(B_117)
      | k1_relat_1(B_117) = k1_xboole_0
      | ~ v4_relat_1(B_117,k1_tarski(B_116))
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_28,c_197])).

tff(c_438,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_3')
    | k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_435])).

tff(c_441,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_3')
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_438])).

tff(c_442,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_441])).

tff(c_121,plain,(
    ! [B_49,C_50,A_51] :
      ( r2_hidden(B_49,C_50)
      | ~ r1_tarski(k2_tarski(A_51,B_49),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_130,plain,(
    ! [B_52,A_53] : r2_hidden(B_52,k2_tarski(A_53,B_52)) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_136,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_130])).

tff(c_481,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_136])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_481])).

tff(c_494,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_686,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_689,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_686])).

tff(c_691,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_689])).

tff(c_786,plain,(
    ! [D_172,C_173,A_174,B_175] :
      ( r2_hidden(k1_funct_1(D_172,C_173),k2_relset_1(A_174,B_175,D_172))
      | k1_xboole_0 = B_175
      | ~ r2_hidden(C_173,A_174)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(D_172,A_174,B_175)
      | ~ v1_funct_1(D_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_792,plain,(
    ! [C_173] :
      ( r2_hidden(k1_funct_1('#skF_3',C_173),k1_xboole_0)
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_173,k1_tarski('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')))
      | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_786])).

tff(c_795,plain,(
    ! [C_173] :
      ( r2_hidden(k1_funct_1('#skF_3',C_173),k1_xboole_0)
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_173,k1_tarski('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_792])).

tff(c_797,plain,(
    ! [C_176] :
      ( r2_hidden(k1_funct_1('#skF_3',C_176),k1_xboole_0)
      | ~ r2_hidden(C_176,k1_tarski('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_795])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_803,plain,(
    ! [C_176] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_3',C_176))
      | ~ r2_hidden(C_176,k1_tarski('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_797,c_36])).

tff(c_808,plain,(
    ! [C_177] : ~ r2_hidden(C_177,k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_803])).

tff(c_818,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_533,c_808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:14:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.45  
% 3.06/1.45  %Foreground sorts:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Background operators:
% 3.06/1.45  
% 3.06/1.45  
% 3.06/1.45  %Foreground operators:
% 3.06/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.06/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.45  
% 3.06/1.47  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.06/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.47  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.06/1.47  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.06/1.47  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.06/1.47  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.06/1.47  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.06/1.47  tff(f_72, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.06/1.47  tff(f_61, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.06/1.47  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.06/1.47  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.06/1.47  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.06/1.47  tff(f_103, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.06/1.47  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.06/1.47  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.47  tff(c_513, plain, (![B_118, C_119, A_120]: (r2_hidden(B_118, C_119) | ~r1_tarski(k2_tarski(A_120, B_118), C_119))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.47  tff(c_527, plain, (![B_121, A_122]: (r2_hidden(B_121, k2_tarski(A_122, B_121)))), inference(resolution, [status(thm)], [c_6, c_513])).
% 3.06/1.47  tff(c_533, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_527])).
% 3.06/1.47  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.47  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.06/1.47  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.06/1.47  tff(c_54, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.06/1.47  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.06/1.47  tff(c_81, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.06/1.47  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_81])).
% 3.06/1.47  tff(c_192, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.47  tff(c_196, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_192])).
% 3.06/1.47  tff(c_291, plain, (![B_94, C_95, A_96]: (r2_hidden(k1_funct_1(B_94, C_95), A_96) | ~r2_hidden(C_95, k1_relat_1(B_94)) | ~v1_funct_1(B_94) | ~v5_relat_1(B_94, A_96) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.06/1.47  tff(c_48, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.06/1.47  tff(c_300, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_291, c_48])).
% 3.06/1.47  tff(c_305, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_196, c_56, c_300])).
% 3.06/1.47  tff(c_109, plain, (![A_47]: (k1_relat_1(A_47)=k1_xboole_0 | k2_relat_1(A_47)!=k1_xboole_0 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.47  tff(c_113, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_85, c_109])).
% 3.06/1.47  tff(c_119, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_113])).
% 3.06/1.47  tff(c_114, plain, (![A_48]: (k2_relat_1(A_48)=k1_xboole_0 | k1_relat_1(A_48)!=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.47  tff(c_118, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_85, c_114])).
% 3.06/1.47  tff(c_120, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_119, c_118])).
% 3.06/1.47  tff(c_186, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.47  tff(c_190, plain, (v4_relat_1('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_186])).
% 3.06/1.47  tff(c_28, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.47  tff(c_197, plain, (![B_76, A_77]: (k1_tarski(B_76)=A_77 | k1_xboole_0=A_77 | ~r1_tarski(A_77, k1_tarski(B_76)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.47  tff(c_435, plain, (![B_116, B_117]: (k1_tarski(B_116)=k1_relat_1(B_117) | k1_relat_1(B_117)=k1_xboole_0 | ~v4_relat_1(B_117, k1_tarski(B_116)) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_28, c_197])).
% 3.06/1.47  tff(c_438, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3') | k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_190, c_435])).
% 3.06/1.47  tff(c_441, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3') | k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_85, c_438])).
% 3.06/1.47  tff(c_442, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_120, c_441])).
% 3.06/1.47  tff(c_121, plain, (![B_49, C_50, A_51]: (r2_hidden(B_49, C_50) | ~r1_tarski(k2_tarski(A_51, B_49), C_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.47  tff(c_130, plain, (![B_52, A_53]: (r2_hidden(B_52, k2_tarski(A_53, B_52)))), inference(resolution, [status(thm)], [c_6, c_121])).
% 3.06/1.47  tff(c_136, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_130])).
% 3.06/1.47  tff(c_481, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_136])).
% 3.06/1.47  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_481])).
% 3.06/1.47  tff(c_494, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_113])).
% 3.06/1.47  tff(c_686, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.06/1.47  tff(c_689, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_686])).
% 3.06/1.47  tff(c_691, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_494, c_689])).
% 3.06/1.47  tff(c_786, plain, (![D_172, C_173, A_174, B_175]: (r2_hidden(k1_funct_1(D_172, C_173), k2_relset_1(A_174, B_175, D_172)) | k1_xboole_0=B_175 | ~r2_hidden(C_173, A_174) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(D_172, A_174, B_175) | ~v1_funct_1(D_172))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.47  tff(c_792, plain, (![C_173]: (r2_hidden(k1_funct_1('#skF_3', C_173), k1_xboole_0) | k1_xboole_0='#skF_2' | ~r2_hidden(C_173, k1_tarski('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_691, c_786])).
% 3.06/1.47  tff(c_795, plain, (![C_173]: (r2_hidden(k1_funct_1('#skF_3', C_173), k1_xboole_0) | k1_xboole_0='#skF_2' | ~r2_hidden(C_173, k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_792])).
% 3.06/1.47  tff(c_797, plain, (![C_176]: (r2_hidden(k1_funct_1('#skF_3', C_176), k1_xboole_0) | ~r2_hidden(C_176, k1_tarski('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_795])).
% 3.06/1.47  tff(c_36, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.06/1.47  tff(c_803, plain, (![C_176]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_3', C_176)) | ~r2_hidden(C_176, k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_797, c_36])).
% 3.06/1.47  tff(c_808, plain, (![C_177]: (~r2_hidden(C_177, k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_803])).
% 3.06/1.47  tff(c_818, plain, $false, inference(resolution, [status(thm)], [c_533, c_808])).
% 3.06/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  Inference rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Ref     : 0
% 3.06/1.47  #Sup     : 158
% 3.06/1.47  #Fact    : 0
% 3.06/1.47  #Define  : 0
% 3.06/1.47  #Split   : 2
% 3.06/1.47  #Chain   : 0
% 3.06/1.47  #Close   : 0
% 3.06/1.47  
% 3.06/1.47  Ordering : KBO
% 3.06/1.47  
% 3.06/1.47  Simplification rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Subsume      : 20
% 3.06/1.47  #Demod        : 57
% 3.06/1.47  #Tautology    : 50
% 3.06/1.47  #SimpNegUnit  : 5
% 3.06/1.47  #BackRed      : 6
% 3.06/1.47  
% 3.06/1.47  #Partial instantiations: 0
% 3.06/1.47  #Strategies tried      : 1
% 3.06/1.47  
% 3.06/1.47  Timing (in seconds)
% 3.06/1.47  ----------------------
% 3.06/1.47  Preprocessing        : 0.33
% 3.06/1.47  Parsing              : 0.17
% 3.06/1.47  CNF conversion       : 0.02
% 3.06/1.47  Main loop            : 0.36
% 3.06/1.47  Inferencing          : 0.14
% 3.06/1.47  Reduction            : 0.11
% 3.06/1.47  Demodulation         : 0.07
% 3.06/1.47  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.06
% 3.06/1.47  Abstraction          : 0.02
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.47  Total                : 0.73
% 3.06/1.47  Index Insertion      : 0.00
% 3.06/1.47  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
