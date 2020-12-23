%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:59 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 142 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 363 expanded)
%              Number of equality atoms :   24 ( 185 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_35,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4',k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [B_57,C_58,A_59,D_60] :
      ( k1_xboole_0 = B_57
      | r1_tarski(C_58,k8_relset_1(A_59,B_57,D_60,k7_relset_1(A_59,B_57,D_60,C_58)))
      | ~ r1_tarski(C_58,A_59)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_59,B_57)))
      | ~ v1_funct_2(D_60,A_59,B_57)
      | ~ v1_funct_1(D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_59,plain,(
    ! [A_33,B_34,D_35,C_36] :
      ( r1_tarski(k8_relset_1(A_33,B_34,D_35,C_36),A_33)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(D_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,(
    ! [C_36] :
      ( r1_tarski(k8_relset_1('#skF_2','#skF_3','#skF_4',C_36),'#skF_2')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_69,plain,(
    ! [C_37] : r1_tarski(k8_relset_1('#skF_2','#skF_3','#skF_4',C_37),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_64])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    ! [C_37] :
      ( k8_relset_1('#skF_2','#skF_3','#skF_4',C_37) = '#skF_2'
      | ~ r1_tarski('#skF_2',k8_relset_1('#skF_2','#skF_3','#skF_4',C_37)) ) ),
    inference(resolution,[status(thm)],[c_69,c_8])).

tff(c_101,plain,
    ( k8_relset_1('#skF_2','#skF_3','#skF_4',k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_2')) = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_72])).

tff(c_106,plain,
    ( k8_relset_1('#skF_2','#skF_3','#skF_4',k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_2')) = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_12,c_101])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_24,c_106])).

tff(c_110,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_116,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_109])).

tff(c_149,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_4',k7_relset_1('#skF_3','#skF_3','#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_116,c_116,c_116,c_24])).

tff(c_126,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_30])).

tff(c_134,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_28])).

tff(c_20,plain,(
    ! [C_19,B_18,D_20] :
      ( r1_tarski(C_19,k8_relset_1(k1_xboole_0,B_18,D_20,k7_relset_1(k1_xboole_0,B_18,D_20,C_19)))
      | ~ r1_tarski(C_19,k1_xboole_0)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18)))
      | ~ v1_funct_2(D_20,k1_xboole_0,B_18)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_185,plain,(
    ! [C_87,B_88,D_89] :
      ( r1_tarski(C_87,k8_relset_1('#skF_3',B_88,D_89,k7_relset_1('#skF_3',B_88,D_89,C_87)))
      | ~ r1_tarski(C_87,'#skF_3')
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_88)))
      | ~ v1_funct_2(D_89,'#skF_3',B_88)
      | ~ v1_funct_1(D_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_110,c_110,c_110,c_20])).

tff(c_154,plain,(
    ! [A_72,B_73,D_74,C_75] :
      ( r1_tarski(k8_relset_1(A_72,B_73,D_74,C_75),A_72)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_1(D_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_159,plain,(
    ! [C_75] :
      ( r1_tarski(k8_relset_1('#skF_3','#skF_3','#skF_4',C_75),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_154])).

tff(c_164,plain,(
    ! [C_76] : r1_tarski(k8_relset_1('#skF_3','#skF_3','#skF_4',C_76),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_159])).

tff(c_167,plain,(
    ! [C_76] :
      ( k8_relset_1('#skF_3','#skF_3','#skF_4',C_76) = '#skF_3'
      | ~ r1_tarski('#skF_3',k8_relset_1('#skF_3','#skF_3','#skF_4',C_76)) ) ),
    inference(resolution,[status(thm)],[c_164,c_8])).

tff(c_189,plain,
    ( k8_relset_1('#skF_3','#skF_3','#skF_4',k7_relset_1('#skF_3','#skF_3','#skF_4','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_185,c_167])).

tff(c_194,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_4',k7_relset_1('#skF_3','#skF_3','#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_126,c_134,c_12,c_189])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.31  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.31  
% 2.13/1.32  tff(f_89, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 2.13/1.32  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.32  tff(f_76, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_2)).
% 2.13/1.32  tff(f_61, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 2.13/1.32  tff(c_26, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.32  tff(c_35, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_26])).
% 2.13/1.32  tff(c_24, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.32  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.32  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.32  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.32  tff(c_12, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.32  tff(c_97, plain, (![B_57, C_58, A_59, D_60]: (k1_xboole_0=B_57 | r1_tarski(C_58, k8_relset_1(A_59, B_57, D_60, k7_relset_1(A_59, B_57, D_60, C_58))) | ~r1_tarski(C_58, A_59) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_59, B_57))) | ~v1_funct_2(D_60, A_59, B_57) | ~v1_funct_1(D_60))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.13/1.32  tff(c_59, plain, (![A_33, B_34, D_35, C_36]: (r1_tarski(k8_relset_1(A_33, B_34, D_35, C_36), A_33) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(D_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.32  tff(c_64, plain, (![C_36]: (r1_tarski(k8_relset_1('#skF_2', '#skF_3', '#skF_4', C_36), '#skF_2') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_59])).
% 2.13/1.32  tff(c_69, plain, (![C_37]: (r1_tarski(k8_relset_1('#skF_2', '#skF_3', '#skF_4', C_37), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_64])).
% 2.13/1.32  tff(c_8, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.32  tff(c_72, plain, (![C_37]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', C_37)='#skF_2' | ~r1_tarski('#skF_2', k8_relset_1('#skF_2', '#skF_3', '#skF_4', C_37)))), inference(resolution, [status(thm)], [c_69, c_8])).
% 2.13/1.32  tff(c_101, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'))='#skF_2' | k1_xboole_0='#skF_3' | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_97, c_72])).
% 2.13/1.32  tff(c_106, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'))='#skF_2' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_12, c_101])).
% 2.13/1.32  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_24, c_106])).
% 2.13/1.32  tff(c_110, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.13/1.32  tff(c_109, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.13/1.32  tff(c_116, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_109])).
% 2.13/1.32  tff(c_149, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_4', k7_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_116, c_116, c_116, c_24])).
% 2.13/1.32  tff(c_126, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_30])).
% 2.13/1.32  tff(c_134, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_28])).
% 2.13/1.32  tff(c_20, plain, (![C_19, B_18, D_20]: (r1_tarski(C_19, k8_relset_1(k1_xboole_0, B_18, D_20, k7_relset_1(k1_xboole_0, B_18, D_20, C_19))) | ~r1_tarski(C_19, k1_xboole_0) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))) | ~v1_funct_2(D_20, k1_xboole_0, B_18) | ~v1_funct_1(D_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.13/1.32  tff(c_185, plain, (![C_87, B_88, D_89]: (r1_tarski(C_87, k8_relset_1('#skF_3', B_88, D_89, k7_relset_1('#skF_3', B_88, D_89, C_87))) | ~r1_tarski(C_87, '#skF_3') | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_88))) | ~v1_funct_2(D_89, '#skF_3', B_88) | ~v1_funct_1(D_89))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_110, c_110, c_110, c_20])).
% 2.13/1.32  tff(c_154, plain, (![A_72, B_73, D_74, C_75]: (r1_tarski(k8_relset_1(A_72, B_73, D_74, C_75), A_72) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_1(D_74))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.32  tff(c_159, plain, (![C_75]: (r1_tarski(k8_relset_1('#skF_3', '#skF_3', '#skF_4', C_75), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_134, c_154])).
% 2.13/1.32  tff(c_164, plain, (![C_76]: (r1_tarski(k8_relset_1('#skF_3', '#skF_3', '#skF_4', C_76), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_159])).
% 2.13/1.32  tff(c_167, plain, (![C_76]: (k8_relset_1('#skF_3', '#skF_3', '#skF_4', C_76)='#skF_3' | ~r1_tarski('#skF_3', k8_relset_1('#skF_3', '#skF_3', '#skF_4', C_76)))), inference(resolution, [status(thm)], [c_164, c_8])).
% 2.13/1.32  tff(c_189, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_4', k7_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_185, c_167])).
% 2.13/1.32  tff(c_194, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_4', k7_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_126, c_134, c_12, c_189])).
% 2.13/1.32  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_194])).
% 2.13/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  Inference rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Ref     : 0
% 2.13/1.32  #Sup     : 32
% 2.13/1.32  #Fact    : 0
% 2.13/1.32  #Define  : 0
% 2.13/1.32  #Split   : 4
% 2.13/1.32  #Chain   : 0
% 2.13/1.32  #Close   : 0
% 2.13/1.32  
% 2.13/1.32  Ordering : KBO
% 2.13/1.32  
% 2.13/1.32  Simplification rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Subsume      : 0
% 2.13/1.32  #Demod        : 30
% 2.13/1.32  #Tautology    : 11
% 2.13/1.32  #SimpNegUnit  : 2
% 2.13/1.32  #BackRed      : 3
% 2.13/1.32  
% 2.13/1.32  #Partial instantiations: 0
% 2.13/1.32  #Strategies tried      : 1
% 2.13/1.32  
% 2.13/1.32  Timing (in seconds)
% 2.13/1.32  ----------------------
% 2.13/1.33  Preprocessing        : 0.28
% 2.13/1.33  Parsing              : 0.15
% 2.13/1.33  CNF conversion       : 0.02
% 2.13/1.33  Main loop            : 0.19
% 2.13/1.33  Inferencing          : 0.07
% 2.13/1.33  Reduction            : 0.06
% 2.13/1.33  Demodulation         : 0.04
% 2.13/1.33  BG Simplification    : 0.01
% 2.13/1.33  Subsumption          : 0.04
% 2.13/1.33  Abstraction          : 0.01
% 2.13/1.33  MUC search           : 0.00
% 2.13/1.33  Cooper               : 0.00
% 2.13/1.33  Total                : 0.51
% 2.13/1.33  Index Insertion      : 0.00
% 2.13/1.33  Index Deletion       : 0.00
% 2.13/1.33  Index Matching       : 0.00
% 2.13/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
