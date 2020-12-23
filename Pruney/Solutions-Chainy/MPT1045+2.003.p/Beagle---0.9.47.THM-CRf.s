%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:05 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 137 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 353 expanded)
%              Number of equality atoms :   32 ( 178 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [C_10,A_11,B_12] :
      ( k3_partfun1(C_10,A_11,B_12) = C_10
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_28,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_25])).

tff(c_12,plain,(
    k5_partfun1('#skF_1','#skF_2',k3_partfun1('#skF_3','#skF_1','#skF_2')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_29,plain,(
    k5_partfun1('#skF_1','#skF_2','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_14,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_21,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_18,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_35,plain,(
    ! [B_15,C_16,A_17] :
      ( k1_xboole_0 = B_15
      | v1_partfun1(C_16,A_17)
      | ~ v1_funct_2(C_16,A_17,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_15)))
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_35])).

tff(c_41,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_38])).

tff(c_42,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_41])).

tff(c_50,plain,(
    ! [A_21,B_22,C_23] :
      ( k5_partfun1(A_21,B_22,C_23) = k1_tarski(C_23)
      | ~ v1_partfun1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_56,plain,(
    k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_42,c_53])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_56])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_65,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_16])).

tff(c_73,plain,(
    ! [C_24,A_25,B_26] :
      ( k3_partfun1(C_24,A_25,B_26) = C_24
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_79,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_76])).

tff(c_72,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_3','#skF_1','#skF_1')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_12])).

tff(c_80,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_72])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_18])).

tff(c_2,plain,(
    ! [C_3,B_2] :
      ( v1_partfun1(C_3,k1_xboole_0)
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    ! [C_27,B_28] :
      ( v1_partfun1(C_27,'#skF_1')
      | ~ v1_funct_2(C_27,'#skF_1',B_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_28)))
      | ~ v1_funct_1(C_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_59,c_2])).

tff(c_89,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_86])).

tff(c_92,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66,c_89])).

tff(c_109,plain,(
    ! [A_35,B_36,C_37] :
      ( k5_partfun1(A_35,B_36,C_37) = k1_tarski(C_37)
      | ~ v1_partfun1(C_37,A_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_109])).

tff(c_115,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_92,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:11:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.16  
% 1.84/1.16  %Foreground sorts:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Background operators:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Foreground operators:
% 1.84/1.16  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.84/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.84/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.84/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.16  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.84/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.16  
% 1.84/1.17  tff(f_69, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k5_partfun1(A, B, k3_partfun1(C, A, B)) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t161_funct_2)).
% 1.84/1.17  tff(f_56, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 1.84/1.17  tff(f_42, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 1.84/1.17  tff(f_50, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 1.84/1.17  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.84/1.17  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.84/1.17  tff(c_22, plain, (![C_10, A_11, B_12]: (k3_partfun1(C_10, A_11, B_12)=C_10 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.17  tff(c_25, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_22])).
% 1.84/1.17  tff(c_28, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_25])).
% 1.84/1.17  tff(c_12, plain, (k5_partfun1('#skF_1', '#skF_2', k3_partfun1('#skF_3', '#skF_1', '#skF_2'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.84/1.17  tff(c_29, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 1.84/1.17  tff(c_14, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.84/1.17  tff(c_21, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_14])).
% 1.84/1.17  tff(c_18, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.84/1.17  tff(c_35, plain, (![B_15, C_16, A_17]: (k1_xboole_0=B_15 | v1_partfun1(C_16, A_17) | ~v1_funct_2(C_16, A_17, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_15))) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.17  tff(c_38, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_35])).
% 1.84/1.17  tff(c_41, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_38])).
% 1.84/1.17  tff(c_42, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_21, c_41])).
% 1.84/1.17  tff(c_50, plain, (![A_21, B_22, C_23]: (k5_partfun1(A_21, B_22, C_23)=k1_tarski(C_23) | ~v1_partfun1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.17  tff(c_53, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_50])).
% 1.84/1.17  tff(c_56, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_42, c_53])).
% 1.84/1.17  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_56])).
% 1.84/1.17  tff(c_59, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 1.84/1.17  tff(c_60, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14])).
% 1.84/1.17  tff(c_65, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60])).
% 1.84/1.17  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_16])).
% 1.84/1.17  tff(c_73, plain, (![C_24, A_25, B_26]: (k3_partfun1(C_24, A_25, B_26)=C_24 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.17  tff(c_76, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_73])).
% 1.84/1.17  tff(c_79, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_76])).
% 1.84/1.17  tff(c_72, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_3', '#skF_1', '#skF_1'))!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_12])).
% 1.84/1.17  tff(c_80, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_72])).
% 1.84/1.17  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_18])).
% 1.84/1.17  tff(c_2, plain, (![C_3, B_2]: (v1_partfun1(C_3, k1_xboole_0) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.17  tff(c_86, plain, (![C_27, B_28]: (v1_partfun1(C_27, '#skF_1') | ~v1_funct_2(C_27, '#skF_1', B_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_28))) | ~v1_funct_1(C_27))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_59, c_2])).
% 1.84/1.17  tff(c_89, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_86])).
% 1.84/1.17  tff(c_92, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66, c_89])).
% 1.84/1.17  tff(c_109, plain, (![A_35, B_36, C_37]: (k5_partfun1(A_35, B_36, C_37)=k1_tarski(C_37) | ~v1_partfun1(C_37, A_35) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.17  tff(c_112, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_109])).
% 1.84/1.17  tff(c_115, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_92, c_112])).
% 1.84/1.17  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_115])).
% 1.84/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  Inference rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Ref     : 0
% 1.84/1.17  #Sup     : 17
% 1.84/1.17  #Fact    : 0
% 1.84/1.17  #Define  : 0
% 1.84/1.17  #Split   : 1
% 1.84/1.17  #Chain   : 0
% 1.84/1.17  #Close   : 0
% 1.84/1.17  
% 1.84/1.17  Ordering : KBO
% 1.84/1.17  
% 1.84/1.17  Simplification rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Subsume      : 2
% 1.84/1.17  #Demod        : 28
% 1.84/1.17  #Tautology    : 9
% 1.84/1.17  #SimpNegUnit  : 3
% 1.84/1.17  #BackRed      : 3
% 1.84/1.17  
% 1.84/1.17  #Partial instantiations: 0
% 1.84/1.17  #Strategies tried      : 1
% 1.84/1.17  
% 1.84/1.17  Timing (in seconds)
% 1.84/1.17  ----------------------
% 1.84/1.18  Preprocessing        : 0.29
% 1.84/1.18  Parsing              : 0.15
% 1.84/1.18  CNF conversion       : 0.02
% 1.84/1.18  Main loop            : 0.13
% 1.84/1.18  Inferencing          : 0.04
% 1.84/1.18  Reduction            : 0.04
% 1.84/1.18  Demodulation         : 0.03
% 1.84/1.18  BG Simplification    : 0.01
% 1.84/1.18  Subsumption          : 0.02
% 1.84/1.18  Abstraction          : 0.01
% 1.84/1.18  MUC search           : 0.00
% 1.84/1.18  Cooper               : 0.00
% 1.84/1.18  Total                : 0.44
% 1.84/1.18  Index Insertion      : 0.00
% 1.84/1.18  Index Deletion       : 0.00
% 1.84/1.18  Index Matching       : 0.00
% 1.84/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
