%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:24 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   59 (  80 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 143 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_154,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_28,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_118,plain,(
    ! [C_55,A_56,B_57,D_58] :
      ( r1_tarski(C_55,k1_relset_1(A_56,B_57,D_58))
      | ~ r1_tarski(k6_relat_1(C_55),D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_125,plain,(
    ! [A_59,B_60] :
      ( r1_tarski('#skF_2',k1_relset_1(A_59,B_60,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_128,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_125])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_128])).

tff(c_133,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_159,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_133])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_153,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_149])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_202,plain,(
    ! [C_83,A_84,B_85,D_86] :
      ( r1_tarski(C_83,k2_relset_1(A_84,B_85,D_86))
      | ~ r1_tarski(k6_relat_1(C_83),D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_209,plain,(
    ! [A_87,B_88] :
      ( r1_tarski('#skF_2',k2_relset_1(A_87,B_88,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(resolution,[status(thm)],[c_30,c_202])).

tff(c_212,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_209])).

tff(c_214,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_212])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_61,C_62,B_63] :
      ( r2_xboole_0(A_61,C_62)
      | ~ r2_xboole_0(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    ! [A_61,B_2,A_1] :
      ( r2_xboole_0(A_61,B_2)
      | ~ r1_tarski(A_61,A_1)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_135])).

tff(c_218,plain,(
    ! [B_89] :
      ( r2_xboole_0('#skF_2',B_89)
      | k2_relat_1('#skF_3') = B_89
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_89) ) ),
    inference(resolution,[status(thm)],[c_214,c_138])).

tff(c_222,plain,(
    ! [A_9] :
      ( r2_xboole_0('#skF_2',A_9)
      | k2_relat_1('#skF_3') = A_9
      | ~ v5_relat_1('#skF_3',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_218])).

tff(c_244,plain,(
    ! [A_92] :
      ( r2_xboole_0('#skF_2',A_92)
      | k2_relat_1('#skF_3') = A_92
      | ~ v5_relat_1('#skF_3',A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_222])).

tff(c_247,plain,
    ( r2_xboole_0('#skF_2','#skF_2')
    | k2_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_153,c_244])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_4,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.73  
% 2.70/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.74  %$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.74  
% 2.70/1.74  %Foreground sorts:
% 2.70/1.74  
% 2.70/1.74  
% 2.70/1.74  %Background operators:
% 2.70/1.74  
% 2.70/1.74  
% 2.70/1.74  %Foreground operators:
% 2.70/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.70/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.70/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.74  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.70/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.70/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.74  
% 2.70/1.76  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 2.70/1.76  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.70/1.76  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.70/1.76  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.70/1.76  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.70/1.76  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.70/1.76  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.70/1.76  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.70/1.76  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l58_xboole_1)).
% 2.70/1.76  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.76  tff(c_154, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.76  tff(c_158, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_154])).
% 2.70/1.76  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.76  tff(c_55, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.70/1.76  tff(c_30, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.76  tff(c_118, plain, (![C_55, A_56, B_57, D_58]: (r1_tarski(C_55, k1_relset_1(A_56, B_57, D_58)) | ~r1_tarski(k6_relat_1(C_55), D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.76  tff(c_125, plain, (![A_59, B_60]: (r1_tarski('#skF_2', k1_relset_1(A_59, B_60, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(resolution, [status(thm)], [c_30, c_118])).
% 2.70/1.76  tff(c_128, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_125])).
% 2.70/1.76  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_128])).
% 2.70/1.76  tff(c_133, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.70/1.76  tff(c_159, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_133])).
% 2.70/1.76  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.76  tff(c_149, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.70/1.76  tff(c_153, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_149])).
% 2.70/1.76  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.76  tff(c_47, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.76  tff(c_50, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.70/1.76  tff(c_53, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 2.70/1.76  tff(c_14, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.70/1.76  tff(c_202, plain, (![C_83, A_84, B_85, D_86]: (r1_tarski(C_83, k2_relset_1(A_84, B_85, D_86)) | ~r1_tarski(k6_relat_1(C_83), D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.76  tff(c_209, plain, (![A_87, B_88]: (r1_tarski('#skF_2', k2_relset_1(A_87, B_88, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(resolution, [status(thm)], [c_30, c_202])).
% 2.70/1.76  tff(c_212, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_209])).
% 2.70/1.76  tff(c_214, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_212])).
% 2.70/1.76  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.76  tff(c_135, plain, (![A_61, C_62, B_63]: (r2_xboole_0(A_61, C_62) | ~r2_xboole_0(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.70/1.76  tff(c_138, plain, (![A_61, B_2, A_1]: (r2_xboole_0(A_61, B_2) | ~r1_tarski(A_61, A_1) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_135])).
% 2.70/1.76  tff(c_218, plain, (![B_89]: (r2_xboole_0('#skF_2', B_89) | k2_relat_1('#skF_3')=B_89 | ~r1_tarski(k2_relat_1('#skF_3'), B_89))), inference(resolution, [status(thm)], [c_214, c_138])).
% 2.70/1.76  tff(c_222, plain, (![A_9]: (r2_xboole_0('#skF_2', A_9) | k2_relat_1('#skF_3')=A_9 | ~v5_relat_1('#skF_3', A_9) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_218])).
% 2.70/1.76  tff(c_244, plain, (![A_92]: (r2_xboole_0('#skF_2', A_92) | k2_relat_1('#skF_3')=A_92 | ~v5_relat_1('#skF_3', A_92))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_222])).
% 2.70/1.76  tff(c_247, plain, (r2_xboole_0('#skF_2', '#skF_2') | k2_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_153, c_244])).
% 2.70/1.76  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_4, c_247])).
% 2.70/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.76  
% 2.70/1.76  Inference rules
% 2.70/1.76  ----------------------
% 2.70/1.76  #Ref     : 0
% 2.70/1.76  #Sup     : 48
% 2.70/1.76  #Fact    : 0
% 2.70/1.76  #Define  : 0
% 2.70/1.76  #Split   : 3
% 2.70/1.76  #Chain   : 0
% 2.70/1.76  #Close   : 0
% 2.70/1.76  
% 2.70/1.76  Ordering : KBO
% 2.70/1.76  
% 2.70/1.76  Simplification rules
% 2.70/1.76  ----------------------
% 2.70/1.76  #Subsume      : 4
% 2.70/1.76  #Demod        : 4
% 2.70/1.76  #Tautology    : 8
% 2.70/1.76  #SimpNegUnit  : 3
% 2.70/1.76  #BackRed      : 1
% 2.70/1.76  
% 2.70/1.76  #Partial instantiations: 0
% 2.70/1.76  #Strategies tried      : 1
% 2.70/1.76  
% 2.70/1.76  Timing (in seconds)
% 2.70/1.76  ----------------------
% 2.70/1.77  Preprocessing        : 0.49
% 2.70/1.77  Parsing              : 0.25
% 2.70/1.77  CNF conversion       : 0.03
% 2.70/1.77  Main loop            : 0.37
% 2.70/1.77  Inferencing          : 0.14
% 2.70/1.77  Reduction            : 0.10
% 2.70/1.77  Demodulation         : 0.07
% 2.70/1.77  BG Simplification    : 0.02
% 2.70/1.77  Subsumption          : 0.08
% 2.70/1.77  Abstraction          : 0.02
% 2.70/1.77  MUC search           : 0.00
% 2.70/1.77  Cooper               : 0.00
% 2.70/1.77  Total                : 0.91
% 2.70/1.77  Index Insertion      : 0.00
% 2.70/1.77  Index Deletion       : 0.00
% 2.70/1.77  Index Matching       : 0.00
% 2.70/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
