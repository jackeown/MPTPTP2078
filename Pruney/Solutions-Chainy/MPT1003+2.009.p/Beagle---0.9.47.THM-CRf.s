%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:59 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 167 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 407 expanded)
%              Number of equality atoms :   46 ( 239 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] :
      ( k7_relset_1(A_10,B_11,C_12,A_10) = k2_relset_1(A_10,B_11,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_14,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_14])).

tff(c_16,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_23,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    ! [A_13,B_14,C_15] :
      ( k8_relset_1(A_13,B_14,C_15,B_14) = k1_relset_1(A_13,B_14,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_33])).

tff(c_56,plain,(
    ! [B_24,A_25,C_26] :
      ( k1_xboole_0 = B_24
      | k8_relset_1(A_25,B_24,C_26,B_24) = A_25
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_25,B_24)))
      | ~ v1_funct_2(C_26,A_25,B_24)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_56])).

tff(c_61,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_36,c_58])).

tff(c_62,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_23,c_61])).

tff(c_51,plain,(
    ! [B_21,A_22,C_23] :
      ( k8_relset_1(B_21,A_22,C_23,k7_relset_1(B_21,A_22,C_23,B_21)) = k1_relset_1(B_21,A_22,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(B_21,A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_55,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_3')) = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_53])).

tff(c_74,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_55])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_74])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_82,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_77])).

tff(c_83,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_18])).

tff(c_98,plain,(
    ! [A_30,B_31,C_32] :
      ( k7_relset_1(A_30,B_31,C_32,A_30) = k2_relset_1(A_30,B_31,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_98])).

tff(c_89,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_14])).

tff(c_102,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k2_relset_1('#skF_1','#skF_1','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_89])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_20])).

tff(c_90,plain,(
    ! [A_27,B_28,C_29] :
      ( k8_relset_1(A_27,B_28,C_29,B_28) = k1_relset_1(A_27,B_28,C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_90])).

tff(c_10,plain,(
    ! [B_8,C_9] :
      ( k8_relset_1(k1_xboole_0,B_8,C_9,B_8) = k1_xboole_0
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_8)))
      | ~ v1_funct_2(C_9,k1_xboole_0,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_33,C_34] :
      ( k8_relset_1('#skF_1',B_33,C_34,B_33) = '#skF_1'
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_33)))
      | ~ v1_funct_2(C_34,'#skF_1',B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_76,c_76,c_76,c_10])).

tff(c_110,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_108])).

tff(c_113,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_84,c_93,c_110])).

tff(c_123,plain,(
    ! [B_35,A_36,C_37] :
      ( k8_relset_1(B_35,A_36,C_37,k7_relset_1(B_35,A_36,C_37,B_35)) = k1_relset_1(B_35,A_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(B_35,A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) = k1_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_123])).

tff(c_127,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k2_relset_1('#skF_1','#skF_1','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_101,c_125])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.87/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.87/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.87/1.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.87/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.18  
% 1.87/1.19  tff(f_62, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 1.87/1.19  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 1.87/1.19  tff(f_49, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 1.87/1.19  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 1.87/1.19  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.19  tff(c_24, plain, (![A_10, B_11, C_12]: (k7_relset_1(A_10, B_11, C_12, A_10)=k2_relset_1(A_10, B_11, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_27, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_24])).
% 1.87/1.19  tff(c_14, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.19  tff(c_28, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27, c_14])).
% 1.87/1.19  tff(c_16, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.19  tff(c_23, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 1.87/1.19  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.19  tff(c_20, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.19  tff(c_33, plain, (![A_13, B_14, C_15]: (k8_relset_1(A_13, B_14, C_15, B_14)=k1_relset_1(A_13, B_14, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_36, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_33])).
% 1.87/1.19  tff(c_56, plain, (![B_24, A_25, C_26]: (k1_xboole_0=B_24 | k8_relset_1(A_25, B_24, C_26, B_24)=A_25 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_25, B_24))) | ~v1_funct_2(C_26, A_25, B_24) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.19  tff(c_58, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_56])).
% 1.87/1.19  tff(c_61, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_36, c_58])).
% 1.87/1.19  tff(c_62, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_23, c_61])).
% 1.87/1.19  tff(c_51, plain, (![B_21, A_22, C_23]: (k8_relset_1(B_21, A_22, C_23, k7_relset_1(B_21, A_22, C_23, B_21))=k1_relset_1(B_21, A_22, C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(B_21, A_22))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.19  tff(c_53, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_51])).
% 1.87/1.19  tff(c_55, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_27, c_53])).
% 1.87/1.19  tff(c_74, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_55])).
% 1.87/1.19  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_74])).
% 1.87/1.19  tff(c_76, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 1.87/1.19  tff(c_77, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16])).
% 1.87/1.19  tff(c_82, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_77])).
% 1.87/1.19  tff(c_83, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_18])).
% 1.87/1.19  tff(c_98, plain, (![A_30, B_31, C_32]: (k7_relset_1(A_30, B_31, C_32, A_30)=k2_relset_1(A_30, B_31, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_101, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_83, c_98])).
% 1.87/1.19  tff(c_89, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_14])).
% 1.87/1.19  tff(c_102, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k2_relset_1('#skF_1', '#skF_1', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_89])).
% 1.87/1.19  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_20])).
% 1.87/1.19  tff(c_90, plain, (![A_27, B_28, C_29]: (k8_relset_1(A_27, B_28, C_29, B_28)=k1_relset_1(A_27, B_28, C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_93, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_83, c_90])).
% 1.87/1.19  tff(c_10, plain, (![B_8, C_9]: (k8_relset_1(k1_xboole_0, B_8, C_9, B_8)=k1_xboole_0 | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_8))) | ~v1_funct_2(C_9, k1_xboole_0, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.19  tff(c_108, plain, (![B_33, C_34]: (k8_relset_1('#skF_1', B_33, C_34, B_33)='#skF_1' | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_33))) | ~v1_funct_2(C_34, '#skF_1', B_33) | ~v1_funct_1(C_34))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_76, c_76, c_76, c_10])).
% 1.87/1.19  tff(c_110, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_83, c_108])).
% 1.87/1.19  tff(c_113, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_84, c_93, c_110])).
% 1.87/1.19  tff(c_123, plain, (![B_35, A_36, C_37]: (k8_relset_1(B_35, A_36, C_37, k7_relset_1(B_35, A_36, C_37, B_35))=k1_relset_1(B_35, A_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(B_35, A_36))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.19  tff(c_125, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))=k1_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_83, c_123])).
% 1.87/1.19  tff(c_127, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k2_relset_1('#skF_1', '#skF_1', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_101, c_125])).
% 1.87/1.19  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_127])).
% 1.87/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  Inference rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Ref     : 0
% 1.87/1.19  #Sup     : 31
% 1.87/1.19  #Fact    : 0
% 1.87/1.19  #Define  : 0
% 1.87/1.19  #Split   : 1
% 1.87/1.19  #Chain   : 0
% 1.87/1.19  #Close   : 0
% 1.87/1.19  
% 1.87/1.19  Ordering : KBO
% 1.87/1.19  
% 1.87/1.19  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 0
% 1.87/1.19  #Demod        : 26
% 1.87/1.19  #Tautology    : 23
% 1.87/1.19  #SimpNegUnit  : 3
% 1.87/1.19  #BackRed      : 7
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.87/1.19  Preprocessing        : 0.28
% 1.87/1.19  Parsing              : 0.14
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.13
% 1.87/1.19  Inferencing          : 0.04
% 1.87/1.19  Reduction            : 0.04
% 1.87/1.19  Demodulation         : 0.03
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.02
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.44
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.20  Index Deletion       : 0.00
% 1.87/1.20  Index Matching       : 0.00
% 1.87/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
