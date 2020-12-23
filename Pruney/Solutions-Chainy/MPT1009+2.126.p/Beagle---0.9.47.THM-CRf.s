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
% DateTime   : Thu Dec  3 10:14:59 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 317 expanded)
%              Number of leaves         :   41 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 677 expanded)
%              Number of equality atoms :   39 ( 150 expanded)
%              Maximal formula depth    :    9 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_38,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_138,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_138])).

tff(c_147,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_141])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k9_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1274,plain,(
    ! [B_164,A_165] :
      ( k1_tarski(k1_funct_1(B_164,A_165)) = k2_relat_1(B_164)
      | k1_tarski(A_165) != k1_relat_1(B_164)
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1283,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_60])).

tff(c_1289,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_68,c_1283])).

tff(c_1326,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1289])).

tff(c_270,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_284,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_270])).

tff(c_332,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(k1_relat_1(B_84),A_85)
      | ~ v4_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1869,plain,(
    ! [B_237,B_238] :
      ( k1_tarski(B_237) = k1_relat_1(B_238)
      | k1_relat_1(B_238) = k1_xboole_0
      | ~ v4_relat_1(B_238,k1_tarski(B_237))
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_332,c_16])).

tff(c_1899,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_284,c_1869])).

tff(c_1912,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1899])).

tff(c_1913,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1326,c_1912])).

tff(c_1195,plain,(
    ! [A_160] :
      ( m1_subset_1(A_160,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_160),k2_relat_1(A_160))))
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1219,plain,(
    ! [A_160] :
      ( r1_tarski(A_160,k2_zfmisc_1(k1_relat_1(A_160),k2_relat_1(A_160)))
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_1195,c_28])).

tff(c_1939,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1913,c_1219])).

tff(c_1975,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_68,c_26,c_1939])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_165])).

tff(c_2093,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1975,c_177])).

tff(c_2159,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_8])).

tff(c_83,plain,(
    ! [A_39] : k2_zfmisc_1(A_39,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_38])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_202,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(k9_relat_1(B_57,A_58),k2_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_210,plain,(
    ! [A_58] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_58),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_202])).

tff(c_224,plain,(
    ! [A_62] : r1_tarski(k9_relat_1(k1_xboole_0,A_62),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_210])).

tff(c_233,plain,(
    ! [A_62] : k9_relat_1(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_224,c_177])).

tff(c_2153,plain,(
    ! [A_62] : k9_relat_1('#skF_4',A_62) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_2093,c_233])).

tff(c_1376,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k7_relset_1(A_175,B_176,C_177,D_178) = k9_relat_1(C_177,D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1389,plain,(
    ! [D_178] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_178) = k9_relat_1('#skF_4',D_178) ),
    inference(resolution,[status(thm)],[c_64,c_1376])).

tff(c_1401,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_60])).

tff(c_2386,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2153,c_1401])).

tff(c_2390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2159,c_2386])).

tff(c_2392,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1289])).

tff(c_2397,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_64])).

tff(c_2468,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( k7_relset_1(A_249,B_250,C_251,D_252) = k9_relat_1(C_251,D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2480,plain,(
    ! [D_252] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_252) = k9_relat_1('#skF_4',D_252) ),
    inference(resolution,[status(thm)],[c_2397,c_2468])).

tff(c_2391,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1289])).

tff(c_2467,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_2391])).

tff(c_2507,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2480,c_2467])).

tff(c_2525,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2507])).

tff(c_2529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:04:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.71  
% 4.16/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.16/1.71  
% 4.16/1.71  %Foreground sorts:
% 4.16/1.71  
% 4.16/1.71  
% 4.16/1.71  %Background operators:
% 4.16/1.71  
% 4.16/1.71  
% 4.16/1.71  %Foreground operators:
% 4.16/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.16/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.16/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.71  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.16/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.16/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.16/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.16/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.16/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.16/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.71  
% 4.16/1.72  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.16/1.72  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.16/1.72  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.16/1.72  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.16/1.72  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.16/1.72  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.16/1.72  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.16/1.72  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.16/1.72  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.16/1.72  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.16/1.72  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.16/1.72  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.16/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.16/1.72  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.16/1.72  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.16/1.72  tff(c_38, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.16/1.72  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.16/1.72  tff(c_138, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.16/1.72  tff(c_141, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_138])).
% 4.16/1.72  tff(c_147, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_141])).
% 4.16/1.72  tff(c_40, plain, (![B_24, A_23]: (r1_tarski(k9_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.16/1.72  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.16/1.72  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.16/1.72  tff(c_1274, plain, (![B_164, A_165]: (k1_tarski(k1_funct_1(B_164, A_165))=k2_relat_1(B_164) | k1_tarski(A_165)!=k1_relat_1(B_164) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.16/1.72  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.16/1.72  tff(c_1283, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1274, c_60])).
% 4.16/1.72  tff(c_1289, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_68, c_1283])).
% 4.16/1.72  tff(c_1326, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1289])).
% 4.16/1.72  tff(c_270, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.16/1.72  tff(c_284, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_270])).
% 4.16/1.72  tff(c_332, plain, (![B_84, A_85]: (r1_tarski(k1_relat_1(B_84), A_85) | ~v4_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.16/1.72  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.16/1.72  tff(c_1869, plain, (![B_237, B_238]: (k1_tarski(B_237)=k1_relat_1(B_238) | k1_relat_1(B_238)=k1_xboole_0 | ~v4_relat_1(B_238, k1_tarski(B_237)) | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_332, c_16])).
% 4.16/1.72  tff(c_1899, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_284, c_1869])).
% 4.16/1.72  tff(c_1912, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1899])).
% 4.16/1.72  tff(c_1913, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1326, c_1912])).
% 4.16/1.72  tff(c_1195, plain, (![A_160]: (m1_subset_1(A_160, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_160), k2_relat_1(A_160)))) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.16/1.72  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.16/1.72  tff(c_1219, plain, (![A_160]: (r1_tarski(A_160, k2_zfmisc_1(k1_relat_1(A_160), k2_relat_1(A_160))) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_1195, c_28])).
% 4.16/1.72  tff(c_1939, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1913, c_1219])).
% 4.16/1.72  tff(c_1975, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_68, c_26, c_1939])).
% 4.16/1.72  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.72  tff(c_165, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.72  tff(c_177, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_165])).
% 4.16/1.72  tff(c_2093, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1975, c_177])).
% 4.16/1.72  tff(c_2159, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_8])).
% 4.16/1.72  tff(c_83, plain, (![A_39]: (k2_zfmisc_1(A_39, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.16/1.72  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83, c_38])).
% 4.16/1.72  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.16/1.72  tff(c_202, plain, (![B_57, A_58]: (r1_tarski(k9_relat_1(B_57, A_58), k2_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.16/1.72  tff(c_210, plain, (![A_58]: (r1_tarski(k9_relat_1(k1_xboole_0, A_58), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_202])).
% 4.16/1.72  tff(c_224, plain, (![A_62]: (r1_tarski(k9_relat_1(k1_xboole_0, A_62), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_210])).
% 4.16/1.72  tff(c_233, plain, (![A_62]: (k9_relat_1(k1_xboole_0, A_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_224, c_177])).
% 4.16/1.72  tff(c_2153, plain, (![A_62]: (k9_relat_1('#skF_4', A_62)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_2093, c_233])).
% 4.16/1.72  tff(c_1376, plain, (![A_175, B_176, C_177, D_178]: (k7_relset_1(A_175, B_176, C_177, D_178)=k9_relat_1(C_177, D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.16/1.72  tff(c_1389, plain, (![D_178]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_178)=k9_relat_1('#skF_4', D_178))), inference(resolution, [status(thm)], [c_64, c_1376])).
% 4.16/1.72  tff(c_1401, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_60])).
% 4.16/1.72  tff(c_2386, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2153, c_1401])).
% 4.16/1.72  tff(c_2390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2159, c_2386])).
% 4.16/1.72  tff(c_2392, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1289])).
% 4.16/1.72  tff(c_2397, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_64])).
% 4.16/1.72  tff(c_2468, plain, (![A_249, B_250, C_251, D_252]: (k7_relset_1(A_249, B_250, C_251, D_252)=k9_relat_1(C_251, D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.16/1.72  tff(c_2480, plain, (![D_252]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_252)=k9_relat_1('#skF_4', D_252))), inference(resolution, [status(thm)], [c_2397, c_2468])).
% 4.16/1.72  tff(c_2391, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1289])).
% 4.16/1.72  tff(c_2467, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_2391])).
% 4.16/1.72  tff(c_2507, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2480, c_2467])).
% 4.16/1.72  tff(c_2525, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_2507])).
% 4.16/1.72  tff(c_2529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_2525])).
% 4.16/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.72  
% 4.16/1.72  Inference rules
% 4.16/1.72  ----------------------
% 4.16/1.72  #Ref     : 0
% 4.16/1.72  #Sup     : 498
% 4.16/1.72  #Fact    : 0
% 4.16/1.72  #Define  : 0
% 4.16/1.72  #Split   : 8
% 4.16/1.72  #Chain   : 0
% 4.16/1.72  #Close   : 0
% 4.16/1.72  
% 4.16/1.72  Ordering : KBO
% 4.16/1.72  
% 4.16/1.72  Simplification rules
% 4.16/1.72  ----------------------
% 4.16/1.72  #Subsume      : 82
% 4.16/1.72  #Demod        : 688
% 4.16/1.72  #Tautology    : 269
% 4.16/1.72  #SimpNegUnit  : 19
% 4.16/1.72  #BackRed      : 103
% 4.16/1.72  
% 4.16/1.72  #Partial instantiations: 0
% 4.16/1.72  #Strategies tried      : 1
% 4.16/1.72  
% 4.16/1.72  Timing (in seconds)
% 4.16/1.72  ----------------------
% 4.16/1.73  Preprocessing        : 0.34
% 4.16/1.73  Parsing              : 0.18
% 4.16/1.73  CNF conversion       : 0.02
% 4.16/1.73  Main loop            : 0.63
% 4.16/1.73  Inferencing          : 0.22
% 4.16/1.73  Reduction            : 0.22
% 4.16/1.73  Demodulation         : 0.16
% 4.16/1.73  BG Simplification    : 0.03
% 4.16/1.73  Subsumption          : 0.11
% 4.16/1.73  Abstraction          : 0.03
% 4.16/1.73  MUC search           : 0.00
% 4.16/1.73  Cooper               : 0.00
% 4.16/1.73  Total                : 1.00
% 4.16/1.73  Index Insertion      : 0.00
% 4.16/1.73  Index Deletion       : 0.00
% 4.16/1.73  Index Matching       : 0.00
% 4.16/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
