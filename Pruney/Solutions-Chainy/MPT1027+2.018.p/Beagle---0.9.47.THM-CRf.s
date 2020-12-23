%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:44 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 854 expanded)
%              Number of leaves         :   20 ( 281 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 (2040 expanded)
%              Number of equality atoms :   52 ( 519 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26])).

tff(c_28,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_96,plain,(
    ! [B_26,C_27,A_28] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_28,B_26)
      | k1_relset_1(A_28,B_26,C_27) != A_28
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_96])).

tff(c_108,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_99])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_108])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_120,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_118,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_109,c_8])).

tff(c_86,plain,(
    ! [B_18,A_19] :
      ( v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_91,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_141,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_91])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_141])).

tff(c_147,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_146,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_229,plain,(
    ! [A_34] :
      ( A_34 = '#skF_3'
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_236,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_147,c_229])).

tff(c_65,plain,(
    ! [B_13,A_14] :
      ( ~ v1_xboole_0(B_13)
      | B_13 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_2,c_65])).

tff(c_153,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_146,c_68])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_272,plain,(
    ! [B_38,A_39] :
      ( B_38 = '#skF_3'
      | A_39 = '#skF_3'
      | k2_zfmisc_1(A_39,B_38) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_153,c_153,c_6])).

tff(c_286,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_272])).

tff(c_295,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_306,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_28])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_8,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_155,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_166,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_153,c_155])).

tff(c_170,plain,(
    ! [A_31] :
      ( A_31 = '#skF_3'
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_177,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_147,c_170])).

tff(c_203,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_30])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_203])).

tff(c_208,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_219,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_153,c_208])).

tff(c_303,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_295,c_219])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_153])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,k1_xboole_0,B_9)
      | k1_relset_1(k1_xboole_0,B_9,C_10) != k1_xboole_0
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,k1_xboole_0,B_9)
      | k1_relset_1(k1_xboole_0,B_9,C_10) != k1_xboole_0
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_355,plain,(
    ! [C_45,B_46] :
      ( v1_funct_2(C_45,'#skF_1',B_46)
      | k1_relset_1('#skF_1',B_46,C_45) != '#skF_1'
      | ~ m1_subset_1(C_45,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_304,c_304,c_304,c_36])).

tff(c_376,plain,(
    ! [B_50] :
      ( v1_funct_2('#skF_1','#skF_1',B_50)
      | k1_relset_1('#skF_1',B_50,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_303,c_355])).

tff(c_307,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_34])).

tff(c_379,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_376,c_307])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_379])).

tff(c_385,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_207,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8 ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_269,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_3',A_8,'#skF_3')
      | A_8 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_153,c_153,c_207])).

tff(c_384,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_388,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_34])).

tff(c_401,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_269,c_388])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.06/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.28  
% 2.06/1.29  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.06/1.29  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.06/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.29  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.06/1.29  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.06/1.29  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.06/1.29  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.29  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.29  tff(c_26, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.29  tff(c_34, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26])).
% 2.06/1.29  tff(c_28, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.29  tff(c_96, plain, (![B_26, C_27, A_28]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_28, B_26) | k1_relset_1(A_28, B_26, C_27)!=A_28 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_26))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.29  tff(c_99, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_30, c_96])).
% 2.06/1.29  tff(c_108, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_99])).
% 2.06/1.29  tff(c_109, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_108])).
% 2.06/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.06/1.29  tff(c_120, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2])).
% 2.06/1.29  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.29  tff(c_118, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_109, c_8])).
% 2.06/1.29  tff(c_86, plain, (![B_18, A_19]: (v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_19)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.29  tff(c_90, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_86])).
% 2.06/1.29  tff(c_91, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.06/1.29  tff(c_141, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_91])).
% 2.06/1.29  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_141])).
% 2.06/1.29  tff(c_147, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_90])).
% 2.06/1.29  tff(c_146, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_90])).
% 2.06/1.29  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.29  tff(c_229, plain, (![A_34]: (A_34='#skF_3' | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_146, c_4])).
% 2.06/1.29  tff(c_236, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_147, c_229])).
% 2.06/1.29  tff(c_65, plain, (![B_13, A_14]: (~v1_xboole_0(B_13) | B_13=A_14 | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.29  tff(c_68, plain, (![A_14]: (k1_xboole_0=A_14 | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_2, c_65])).
% 2.06/1.29  tff(c_153, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_146, c_68])).
% 2.06/1.29  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.29  tff(c_272, plain, (![B_38, A_39]: (B_38='#skF_3' | A_39='#skF_3' | k2_zfmisc_1(A_39, B_38)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_153, c_153, c_6])).
% 2.06/1.29  tff(c_286, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_236, c_272])).
% 2.06/1.29  tff(c_295, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_286])).
% 2.06/1.29  tff(c_306, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_28])).
% 2.06/1.29  tff(c_14, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_8, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.29  tff(c_38, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.06/1.29  tff(c_155, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_38])).
% 2.06/1.29  tff(c_166, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_153, c_155])).
% 2.06/1.29  tff(c_170, plain, (![A_31]: (A_31='#skF_3' | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_146, c_4])).
% 2.06/1.29  tff(c_177, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_147, c_170])).
% 2.06/1.29  tff(c_203, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_30])).
% 2.06/1.29  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_203])).
% 2.06/1.29  tff(c_208, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_38])).
% 2.06/1.29  tff(c_219, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_153, c_208])).
% 2.06/1.29  tff(c_303, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_295, c_219])).
% 2.06/1.29  tff(c_304, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_153])).
% 2.06/1.29  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.29  tff(c_18, plain, (![C_10, B_9]: (v1_funct_2(C_10, k1_xboole_0, B_9) | k1_relset_1(k1_xboole_0, B_9, C_10)!=k1_xboole_0 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_9))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.29  tff(c_36, plain, (![C_10, B_9]: (v1_funct_2(C_10, k1_xboole_0, B_9) | k1_relset_1(k1_xboole_0, B_9, C_10)!=k1_xboole_0 | ~m1_subset_1(C_10, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 2.06/1.29  tff(c_355, plain, (![C_45, B_46]: (v1_funct_2(C_45, '#skF_1', B_46) | k1_relset_1('#skF_1', B_46, C_45)!='#skF_1' | ~m1_subset_1(C_45, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_304, c_304, c_304, c_36])).
% 2.06/1.29  tff(c_376, plain, (![B_50]: (v1_funct_2('#skF_1', '#skF_1', B_50) | k1_relset_1('#skF_1', B_50, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_303, c_355])).
% 2.06/1.29  tff(c_307, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_34])).
% 2.06/1.29  tff(c_379, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_376, c_307])).
% 2.06/1.29  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_306, c_379])).
% 2.06/1.29  tff(c_385, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_286])).
% 2.06/1.29  tff(c_207, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8)), inference(splitRight, [status(thm)], [c_38])).
% 2.06/1.29  tff(c_269, plain, (![A_8]: (v1_funct_2('#skF_3', A_8, '#skF_3') | A_8='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_153, c_153, c_207])).
% 2.06/1.29  tff(c_384, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_286])).
% 2.06/1.29  tff(c_388, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_34])).
% 2.06/1.29  tff(c_401, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_269, c_388])).
% 2.06/1.29  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_385, c_401])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 76
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 4
% 2.06/1.29  #Chain   : 0
% 2.06/1.29  #Close   : 0
% 2.06/1.29  
% 2.06/1.29  Ordering : KBO
% 2.06/1.29  
% 2.06/1.29  Simplification rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Subsume      : 5
% 2.06/1.29  #Demod        : 115
% 2.06/1.29  #Tautology    : 66
% 2.06/1.29  #SimpNegUnit  : 3
% 2.06/1.29  #BackRed      : 42
% 2.06/1.29  
% 2.06/1.29  #Partial instantiations: 0
% 2.06/1.29  #Strategies tried      : 1
% 2.06/1.29  
% 2.06/1.29  Timing (in seconds)
% 2.06/1.29  ----------------------
% 2.06/1.29  Preprocessing        : 0.29
% 2.06/1.29  Parsing              : 0.16
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.23
% 2.06/1.29  Inferencing          : 0.08
% 2.06/1.29  Reduction            : 0.07
% 2.06/1.29  Demodulation         : 0.05
% 2.06/1.29  BG Simplification    : 0.01
% 2.06/1.29  Subsumption          : 0.04
% 2.06/1.29  Abstraction          : 0.01
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.30  Total                : 0.55
% 2.06/1.30  Index Insertion      : 0.00
% 2.06/1.30  Index Deletion       : 0.00
% 2.06/1.30  Index Matching       : 0.00
% 2.06/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
