%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:48 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 174 expanded)
%              Number of leaves         :   39 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 312 expanded)
%              Number of equality atoms :   34 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_133,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_133])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_194,plain,(
    ! [A_68] :
      ( k2_relat_1(A_68) = k1_xboole_0
      | k1_relat_1(A_68) != k1_xboole_0
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_206,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_194])).

tff(c_207,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_711,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_725,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_711])).

tff(c_786,plain,(
    ! [A_156,B_157,C_158] :
      ( m1_subset_1(k1_relset_1(A_156,B_157,C_158),k1_zfmisc_1(A_156))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_818,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_786])).

tff(c_831,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_818])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_835,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_831,c_28])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_838,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_835,c_16])).

tff(c_843,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_838])).

tff(c_986,plain,(
    ! [B_169,A_170] :
      ( k1_tarski(k1_funct_1(B_169,A_170)) = k2_relat_1(B_169)
      | k1_tarski(A_170) != k1_relat_1(B_169)
      | ~ v1_funct_1(B_169)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_852,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_62])).

tff(c_54,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k7_relset_1(A_35,B_36,C_37,D_38) = k9_relat_1(C_37,D_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_924,plain,(
    ! [D_38] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_38) = k9_relat_1('#skF_4',D_38) ),
    inference(resolution,[status(thm)],[c_852,c_54])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_850,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_58])).

tff(c_976,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_850])).

tff(c_992,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_976])).

tff(c_1001,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_66,c_843,c_992])).

tff(c_1005,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1001])).

tff(c_1009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1005])).

tff(c_1010,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_1015,plain,(
    ! [A_18] :
      ( r1_tarski(k9_relat_1('#skF_4',A_18),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_36])).

tff(c_1019,plain,(
    ! [A_18] : r1_tarski(k9_relat_1('#skF_4',A_18),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1015])).

tff(c_1398,plain,(
    ! [B_223,A_224] :
      ( B_223 = A_224
      | ~ r1_tarski(B_223,A_224)
      | ~ r1_tarski(A_224,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1402,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_4',A_18) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1('#skF_4',A_18)) ) ),
    inference(resolution,[status(thm)],[c_1019,c_1398])).

tff(c_1416,plain,(
    ! [A_18] : k9_relat_1('#skF_4',A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1402])).

tff(c_2023,plain,(
    ! [A_294,B_295,C_296,D_297] :
      ( k7_relset_1(A_294,B_295,C_296,D_297) = k9_relat_1(C_296,D_297)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2031,plain,(
    ! [D_297] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_297) = k9_relat_1('#skF_4',D_297) ),
    inference(resolution,[status(thm)],[c_62,c_2023])).

tff(c_2043,plain,(
    ! [D_297] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_297) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_2031])).

tff(c_2052,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2043,c_58])).

tff(c_2055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2052])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.63  
% 3.53/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.53/1.63  
% 3.53/1.63  %Foreground sorts:
% 3.53/1.63  
% 3.53/1.63  
% 3.53/1.63  %Background operators:
% 3.53/1.63  
% 3.53/1.63  
% 3.53/1.63  %Foreground operators:
% 3.53/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.53/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.53/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.53/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.63  
% 3.91/1.64  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.91/1.64  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.91/1.64  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.91/1.64  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.91/1.64  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.91/1.64  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.91/1.64  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.91/1.64  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.64  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.91/1.64  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.91/1.64  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.91/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.91/1.64  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.64  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.91/1.64  tff(c_133, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.91/1.64  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_133])).
% 3.91/1.64  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.91/1.64  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.91/1.64  tff(c_194, plain, (![A_68]: (k2_relat_1(A_68)=k1_xboole_0 | k1_relat_1(A_68)!=k1_xboole_0 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.91/1.64  tff(c_206, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_145, c_194])).
% 3.91/1.64  tff(c_207, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_206])).
% 3.91/1.64  tff(c_711, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.91/1.64  tff(c_725, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_711])).
% 3.91/1.64  tff(c_786, plain, (![A_156, B_157, C_158]: (m1_subset_1(k1_relset_1(A_156, B_157, C_158), k1_zfmisc_1(A_156)) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.91/1.64  tff(c_818, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_725, c_786])).
% 3.91/1.64  tff(c_831, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_818])).
% 3.91/1.64  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.91/1.64  tff(c_835, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_831, c_28])).
% 3.91/1.64  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.91/1.64  tff(c_838, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_835, c_16])).
% 3.91/1.64  tff(c_843, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_207, c_838])).
% 3.91/1.64  tff(c_986, plain, (![B_169, A_170]: (k1_tarski(k1_funct_1(B_169, A_170))=k2_relat_1(B_169) | k1_tarski(A_170)!=k1_relat_1(B_169) | ~v1_funct_1(B_169) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.64  tff(c_852, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_62])).
% 3.91/1.64  tff(c_54, plain, (![A_35, B_36, C_37, D_38]: (k7_relset_1(A_35, B_36, C_37, D_38)=k9_relat_1(C_37, D_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.91/1.64  tff(c_924, plain, (![D_38]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_38)=k9_relat_1('#skF_4', D_38))), inference(resolution, [status(thm)], [c_852, c_54])).
% 3.91/1.64  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.91/1.64  tff(c_850, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_58])).
% 3.91/1.64  tff(c_976, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_924, c_850])).
% 3.91/1.64  tff(c_992, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_986, c_976])).
% 3.91/1.64  tff(c_1001, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_66, c_843, c_992])).
% 3.91/1.64  tff(c_1005, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1001])).
% 3.91/1.64  tff(c_1009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_1005])).
% 3.91/1.64  tff(c_1010, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_206])).
% 3.91/1.64  tff(c_1015, plain, (![A_18]: (r1_tarski(k9_relat_1('#skF_4', A_18), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1010, c_36])).
% 3.91/1.64  tff(c_1019, plain, (![A_18]: (r1_tarski(k9_relat_1('#skF_4', A_18), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1015])).
% 3.91/1.64  tff(c_1398, plain, (![B_223, A_224]: (B_223=A_224 | ~r1_tarski(B_223, A_224) | ~r1_tarski(A_224, B_223))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.64  tff(c_1402, plain, (![A_18]: (k9_relat_1('#skF_4', A_18)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1('#skF_4', A_18)))), inference(resolution, [status(thm)], [c_1019, c_1398])).
% 3.91/1.64  tff(c_1416, plain, (![A_18]: (k9_relat_1('#skF_4', A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1402])).
% 3.91/1.64  tff(c_2023, plain, (![A_294, B_295, C_296, D_297]: (k7_relset_1(A_294, B_295, C_296, D_297)=k9_relat_1(C_296, D_297) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.91/1.64  tff(c_2031, plain, (![D_297]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_297)=k9_relat_1('#skF_4', D_297))), inference(resolution, [status(thm)], [c_62, c_2023])).
% 3.91/1.64  tff(c_2043, plain, (![D_297]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_297)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_2031])).
% 3.91/1.64  tff(c_2052, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2043, c_58])).
% 3.91/1.64  tff(c_2055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2052])).
% 3.91/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  Inference rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Ref     : 0
% 3.91/1.64  #Sup     : 410
% 3.91/1.64  #Fact    : 0
% 3.91/1.64  #Define  : 0
% 3.91/1.64  #Split   : 9
% 3.91/1.64  #Chain   : 0
% 3.91/1.64  #Close   : 0
% 3.91/1.64  
% 3.91/1.64  Ordering : KBO
% 3.91/1.64  
% 3.91/1.64  Simplification rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Subsume      : 34
% 3.91/1.64  #Demod        : 232
% 3.91/1.64  #Tautology    : 190
% 3.91/1.64  #SimpNegUnit  : 8
% 3.91/1.64  #BackRed      : 19
% 3.91/1.64  
% 3.91/1.64  #Partial instantiations: 0
% 3.91/1.64  #Strategies tried      : 1
% 3.91/1.64  
% 3.91/1.64  Timing (in seconds)
% 3.91/1.64  ----------------------
% 3.91/1.65  Preprocessing        : 0.33
% 3.91/1.65  Parsing              : 0.17
% 3.91/1.65  CNF conversion       : 0.02
% 3.91/1.65  Main loop            : 0.51
% 3.91/1.65  Inferencing          : 0.19
% 3.91/1.65  Reduction            : 0.17
% 3.91/1.65  Demodulation         : 0.12
% 3.91/1.65  BG Simplification    : 0.02
% 3.91/1.65  Subsumption          : 0.08
% 3.91/1.65  Abstraction          : 0.02
% 3.91/1.65  MUC search           : 0.00
% 3.91/1.65  Cooper               : 0.00
% 3.91/1.65  Total                : 0.88
% 3.91/1.65  Index Insertion      : 0.00
% 3.91/1.65  Index Deletion       : 0.00
% 3.91/1.65  Index Matching       : 0.00
% 3.91/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
