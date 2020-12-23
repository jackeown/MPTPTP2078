%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:05 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   49 (  79 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 158 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k5_partfun1(A,A,k3_partfun1(B,A,A)) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(c_22,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ! [C_32,A_33,B_34] :
      ( k3_partfun1(C_32,A_33,B_34) = C_32
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,
    ( k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_82,plain,(
    k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_79])).

tff(c_16,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_83,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_2') != k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16])).

tff(c_32,plain,(
    ! [C_17,A_18,B_19] :
      ( v1_partfun1(C_17,A_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_37,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    ! [C_20,A_21,B_22] :
      ( k3_partfun1(C_20,A_21,B_22) = C_20
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_41,plain,
    ( k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_38])).

tff(c_44,plain,(
    k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_41])).

tff(c_45,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_2') != k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_57,plain,(
    ! [A_26,B_27,C_28] :
      ( k5_partfun1(A_26,B_27,C_28) = k1_tarski(C_28)
      | ~ v1_partfun1(C_28,A_26)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_57])).

tff(c_63,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_64,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_63])).

tff(c_20,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_partfun1(C_29,A_30)
      | ~ v1_funct_2(C_29,A_30,B_31)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_71,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_68])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_64,c_71])).

tff(c_74,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_102,plain,(
    ! [A_41,B_42,C_43] :
      ( k5_partfun1(A_41,B_42,C_43) = k1_tarski(C_43)
      | ~ v1_partfun1(C_43,A_41)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_108,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_74,c_105])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.21  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.90/1.21  
% 1.90/1.21  %Foreground sorts:
% 1.90/1.21  
% 1.90/1.21  
% 1.90/1.21  %Background operators:
% 1.90/1.21  
% 1.90/1.21  
% 1.90/1.21  %Foreground operators:
% 1.90/1.21  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.90/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.90/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.90/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.21  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.90/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.21  
% 1.90/1.22  tff(f_71, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k5_partfun1(A, A, k3_partfun1(B, A, A)) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_2)).
% 1.90/1.22  tff(f_62, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_partfun1)).
% 1.90/1.22  tff(f_34, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 1.90/1.22  tff(f_56, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_partfun1)).
% 1.90/1.22  tff(f_48, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 1.90/1.22  tff(c_22, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.90/1.22  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.90/1.22  tff(c_76, plain, (![C_32, A_33, B_34]: (k3_partfun1(C_32, A_33, B_34)=C_32 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.22  tff(c_79, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_76])).
% 1.90/1.22  tff(c_82, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_79])).
% 1.90/1.22  tff(c_16, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.97/1.22  tff(c_83, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')!=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_16])).
% 1.97/1.22  tff(c_32, plain, (![C_17, A_18, B_19]: (v1_partfun1(C_17, A_18) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.97/1.22  tff(c_36, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_32])).
% 1.97/1.22  tff(c_37, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_38, plain, (![C_20, A_21, B_22]: (k3_partfun1(C_20, A_21, B_22)=C_20 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.97/1.22  tff(c_41, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_38])).
% 1.97/1.22  tff(c_44, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_41])).
% 1.97/1.22  tff(c_45, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')!=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 1.97/1.22  tff(c_57, plain, (![A_26, B_27, C_28]: (k5_partfun1(A_26, B_27, C_28)=k1_tarski(C_28) | ~v1_partfun1(C_28, A_26) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.22  tff(c_60, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_57])).
% 1.97/1.22  tff(c_63, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_60])).
% 1.97/1.22  tff(c_64, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_45, c_63])).
% 1.97/1.22  tff(c_20, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.97/1.22  tff(c_65, plain, (![C_29, A_30, B_31]: (v1_partfun1(C_29, A_30) | ~v1_funct_2(C_29, A_30, B_31) | ~v1_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.22  tff(c_68, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_65])).
% 1.97/1.22  tff(c_71, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_68])).
% 1.97/1.22  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_64, c_71])).
% 1.97/1.22  tff(c_74, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_102, plain, (![A_41, B_42, C_43]: (k5_partfun1(A_41, B_42, C_43)=k1_tarski(C_43) | ~v1_partfun1(C_43, A_41) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(C_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.22  tff(c_105, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_102])).
% 1.97/1.22  tff(c_108, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_74, c_105])).
% 1.97/1.22  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_108])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 15
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 1
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 2
% 1.97/1.22  #Demod        : 16
% 1.97/1.22  #Tautology    : 8
% 1.97/1.22  #SimpNegUnit  : 3
% 1.97/1.22  #BackRed      : 2
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.23  Preprocessing        : 0.30
% 1.97/1.23  Parsing              : 0.16
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.11
% 1.97/1.23  Inferencing          : 0.05
% 1.97/1.23  Reduction            : 0.03
% 1.97/1.23  Demodulation         : 0.02
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.02
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.44
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
