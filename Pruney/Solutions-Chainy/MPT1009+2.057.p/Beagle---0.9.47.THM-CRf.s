%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:50 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 158 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 295 expanded)
%              Number of equality atoms :   36 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_102,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_114,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,A_14),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_114,c_30])).

tff(c_135,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_351,plain,(
    ! [B_97,A_98] :
      ( k1_tarski(k1_funct_1(B_97,A_98)) = k2_relat_1(B_97)
      | k1_tarski(A_98) != k1_relat_1(B_97)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_273,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_relset_1(A_84,B_85,C_86,D_87) = k9_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_282,plain,(
    ! [D_87] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_87) = k9_relat_1('#skF_4',D_87) ),
    inference(resolution,[status(thm)],[c_46,c_273])).

tff(c_42,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_294,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_42])).

tff(c_357,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_294])).

tff(c_372,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_50,c_357])).

tff(c_382,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_188,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_200,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_188])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_221,plain,(
    ! [B_68,A_69] :
      ( k1_tarski(B_68) = A_69
      | k1_xboole_0 = A_69
      | ~ r1_tarski(A_69,k1_tarski(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_525,plain,(
    ! [B_115,B_116] :
      ( k1_tarski(B_115) = k1_relat_1(B_116)
      | k1_relat_1(B_116) = k1_xboole_0
      | ~ v4_relat_1(B_116,k1_tarski(B_115))
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_22,c_221])).

tff(c_555,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_200,c_525])).

tff(c_582,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_555])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_382,c_582])).

tff(c_585,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_658,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_585])).

tff(c_662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_658])).

tff(c_663,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_668,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_92])).

tff(c_26,plain,(
    ! [A_16] : k9_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_669,plain,(
    ! [A_16] : k9_relat_1('#skF_4',A_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_663,c_26])).

tff(c_670,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_12])).

tff(c_886,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k7_relset_1(A_166,B_167,C_168,D_169) = k9_relat_1(C_168,D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_889,plain,(
    ! [A_166,B_167,D_169] : k7_relset_1(A_166,B_167,'#skF_4',D_169) = k9_relat_1('#skF_4',D_169) ),
    inference(resolution,[status(thm)],[c_670,c_886])).

tff(c_894,plain,(
    ! [A_166,B_167,D_169] : k7_relset_1(A_166,B_167,'#skF_4',D_169) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_889])).

tff(c_906,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_42])).

tff(c_909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:27:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.38  
% 2.93/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.93/1.38  
% 2.93/1.38  %Foreground sorts:
% 2.93/1.38  
% 2.93/1.38  
% 2.93/1.38  %Background operators:
% 2.93/1.38  
% 2.93/1.38  
% 2.93/1.38  %Foreground operators:
% 2.93/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.93/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.93/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.93/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.93/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.93/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.93/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.93/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.93/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.93/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.38  
% 2.93/1.40  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.93/1.40  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.93/1.40  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.93/1.40  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.93/1.40  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.93/1.40  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.93/1.40  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.93/1.40  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.93/1.40  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.93/1.40  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.93/1.40  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.93/1.40  tff(f_59, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.93/1.40  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.40  tff(c_102, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.93/1.40  tff(c_114, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_102])).
% 2.93/1.40  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, A_14), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.93/1.40  tff(c_30, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.93/1.40  tff(c_124, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_114, c_30])).
% 2.93/1.40  tff(c_135, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_124])).
% 2.93/1.40  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.40  tff(c_351, plain, (![B_97, A_98]: (k1_tarski(k1_funct_1(B_97, A_98))=k2_relat_1(B_97) | k1_tarski(A_98)!=k1_relat_1(B_97) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.93/1.40  tff(c_273, plain, (![A_84, B_85, C_86, D_87]: (k7_relset_1(A_84, B_85, C_86, D_87)=k9_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.40  tff(c_282, plain, (![D_87]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_87)=k9_relat_1('#skF_4', D_87))), inference(resolution, [status(thm)], [c_46, c_273])).
% 2.93/1.40  tff(c_42, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.40  tff(c_294, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_42])).
% 2.93/1.40  tff(c_357, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_351, c_294])).
% 2.93/1.40  tff(c_372, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_50, c_357])).
% 2.93/1.40  tff(c_382, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_372])).
% 2.93/1.40  tff(c_188, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.93/1.40  tff(c_200, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_188])).
% 2.93/1.40  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.93/1.40  tff(c_221, plain, (![B_68, A_69]: (k1_tarski(B_68)=A_69 | k1_xboole_0=A_69 | ~r1_tarski(A_69, k1_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.40  tff(c_525, plain, (![B_115, B_116]: (k1_tarski(B_115)=k1_relat_1(B_116) | k1_relat_1(B_116)=k1_xboole_0 | ~v4_relat_1(B_116, k1_tarski(B_115)) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_22, c_221])).
% 2.93/1.40  tff(c_555, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_200, c_525])).
% 2.93/1.40  tff(c_582, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_555])).
% 2.93/1.40  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_382, c_582])).
% 2.93/1.40  tff(c_585, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_372])).
% 2.93/1.40  tff(c_658, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_585])).
% 2.93/1.40  tff(c_662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_658])).
% 2.93/1.40  tff(c_663, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_124])).
% 2.93/1.40  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.40  tff(c_80, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.40  tff(c_92, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_12, c_80])).
% 2.93/1.40  tff(c_668, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_92])).
% 2.93/1.40  tff(c_26, plain, (![A_16]: (k9_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.93/1.40  tff(c_669, plain, (![A_16]: (k9_relat_1('#skF_4', A_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_663, c_663, c_26])).
% 2.93/1.40  tff(c_670, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_12])).
% 2.93/1.40  tff(c_886, plain, (![A_166, B_167, C_168, D_169]: (k7_relset_1(A_166, B_167, C_168, D_169)=k9_relat_1(C_168, D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.40  tff(c_889, plain, (![A_166, B_167, D_169]: (k7_relset_1(A_166, B_167, '#skF_4', D_169)=k9_relat_1('#skF_4', D_169))), inference(resolution, [status(thm)], [c_670, c_886])).
% 2.93/1.40  tff(c_894, plain, (![A_166, B_167, D_169]: (k7_relset_1(A_166, B_167, '#skF_4', D_169)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_669, c_889])).
% 2.93/1.40  tff(c_906, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_894, c_42])).
% 2.93/1.40  tff(c_909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_668, c_906])).
% 2.93/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.40  
% 2.93/1.40  Inference rules
% 2.93/1.40  ----------------------
% 2.93/1.40  #Ref     : 0
% 2.93/1.40  #Sup     : 157
% 2.93/1.40  #Fact    : 0
% 2.93/1.40  #Define  : 0
% 2.93/1.40  #Split   : 6
% 2.93/1.40  #Chain   : 0
% 2.93/1.40  #Close   : 0
% 2.93/1.40  
% 2.93/1.40  Ordering : KBO
% 2.93/1.40  
% 2.93/1.40  Simplification rules
% 2.93/1.40  ----------------------
% 2.93/1.40  #Subsume      : 0
% 2.93/1.40  #Demod        : 111
% 2.93/1.40  #Tautology    : 67
% 2.93/1.40  #SimpNegUnit  : 5
% 2.93/1.40  #BackRed      : 15
% 2.93/1.40  
% 2.93/1.40  #Partial instantiations: 0
% 2.93/1.40  #Strategies tried      : 1
% 2.93/1.40  
% 2.93/1.40  Timing (in seconds)
% 2.93/1.40  ----------------------
% 2.93/1.40  Preprocessing        : 0.31
% 2.93/1.40  Parsing              : 0.17
% 2.93/1.40  CNF conversion       : 0.02
% 2.93/1.40  Main loop            : 0.34
% 2.93/1.40  Inferencing          : 0.13
% 2.93/1.40  Reduction            : 0.11
% 2.93/1.40  Demodulation         : 0.08
% 2.93/1.40  BG Simplification    : 0.02
% 2.93/1.40  Subsumption          : 0.05
% 2.93/1.40  Abstraction          : 0.02
% 2.93/1.40  MUC search           : 0.00
% 2.93/1.40  Cooper               : 0.00
% 2.93/1.40  Total                : 0.68
% 2.93/1.40  Index Insertion      : 0.00
% 2.93/1.40  Index Deletion       : 0.00
% 2.93/1.40  Index Matching       : 0.00
% 2.93/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
