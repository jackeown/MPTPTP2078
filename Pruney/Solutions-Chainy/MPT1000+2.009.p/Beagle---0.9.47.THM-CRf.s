%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:55 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 252 expanded)
%              Number of equality atoms :   35 ( 154 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_49,axiom,(
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

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    ! [A_17,B_18,C_19] :
      ( k8_relset_1(A_17,B_18,C_19,B_18) = k1_relset_1(A_17,B_18,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_40])).

tff(c_18,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_18])).

tff(c_20,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_27,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_49,plain,(
    ! [B_20,A_21,C_22] :
      ( k1_xboole_0 = B_20
      | k1_relset_1(A_21,B_20,C_22) = A_21
      | ~ v1_funct_2(C_22,A_21,B_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_21,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_55,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_27,c_55])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_64,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_59])).

tff(c_70,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_18])).

tff(c_65,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_22])).

tff(c_14,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1('#skF_1',B_26,C_27) = '#skF_1'
      | ~ v1_funct_2(C_27,'#skF_1',B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_58,c_14])).

tff(c_87,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_84])).

tff(c_90,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_87])).

tff(c_103,plain,(
    ! [A_31,B_32,C_33] :
      ( k8_relset_1(A_31,B_32,C_33,B_32) = k1_relset_1(A_31,B_32,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_103])).

tff(c_107,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_105])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:41:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.89/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.89/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.89/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.89/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.21  
% 1.89/1.22  tff(f_62, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 1.89/1.22  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 1.89/1.22  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.89/1.22  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.22  tff(c_40, plain, (![A_17, B_18, C_19]: (k8_relset_1(A_17, B_18, C_19, B_18)=k1_relset_1(A_17, B_18, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.22  tff(c_43, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_40])).
% 1.89/1.22  tff(c_18, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.22  tff(c_44, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_18])).
% 1.89/1.22  tff(c_20, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.22  tff(c_27, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 1.89/1.22  tff(c_24, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.22  tff(c_49, plain, (![B_20, A_21, C_22]: (k1_xboole_0=B_20 | k1_relset_1(A_21, B_20, C_22)=A_21 | ~v1_funct_2(C_22, A_21, B_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_21, B_20))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.22  tff(c_52, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_49])).
% 1.89/1.22  tff(c_55, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52])).
% 1.89/1.22  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_27, c_55])).
% 1.89/1.22  tff(c_58, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 1.89/1.22  tff(c_59, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_20])).
% 1.89/1.22  tff(c_64, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_59])).
% 1.89/1.22  tff(c_70, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_18])).
% 1.89/1.22  tff(c_65, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 1.89/1.22  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_22])).
% 1.89/1.22  tff(c_14, plain, (![B_5, C_6]: (k1_relset_1(k1_xboole_0, B_5, C_6)=k1_xboole_0 | ~v1_funct_2(C_6, k1_xboole_0, B_5) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.22  tff(c_84, plain, (![B_26, C_27]: (k1_relset_1('#skF_1', B_26, C_27)='#skF_1' | ~v1_funct_2(C_27, '#skF_1', B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_26))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_58, c_14])).
% 1.89/1.22  tff(c_87, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_71, c_84])).
% 1.89/1.22  tff(c_90, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_87])).
% 1.89/1.22  tff(c_103, plain, (![A_31, B_32, C_33]: (k8_relset_1(A_31, B_32, C_33, B_32)=k1_relset_1(A_31, B_32, C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.22  tff(c_105, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_103])).
% 1.89/1.22  tff(c_107, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_105])).
% 1.89/1.22  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_107])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 19
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 1
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 0
% 1.89/1.22  #Demod        : 23
% 1.89/1.22  #Tautology    : 13
% 1.89/1.22  #SimpNegUnit  : 2
% 1.89/1.22  #BackRed      : 2
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.22  Preprocessing        : 0.31
% 1.89/1.22  Parsing              : 0.16
% 1.89/1.22  CNF conversion       : 0.02
% 1.89/1.22  Main loop            : 0.14
% 1.89/1.22  Inferencing          : 0.05
% 1.89/1.22  Reduction            : 0.04
% 1.89/1.22  Demodulation         : 0.03
% 1.89/1.22  BG Simplification    : 0.01
% 1.89/1.22  Subsumption          : 0.02
% 1.89/1.22  Abstraction          : 0.01
% 1.89/1.22  MUC search           : 0.00
% 1.89/1.22  Cooper               : 0.00
% 1.89/1.22  Total                : 0.47
% 1.89/1.22  Index Insertion      : 0.00
% 1.89/1.22  Index Deletion       : 0.00
% 1.89/1.22  Index Matching       : 0.00
% 1.89/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
