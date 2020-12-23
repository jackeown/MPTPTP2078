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
% DateTime   : Thu Dec  3 10:17:57 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   48 (  93 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 277 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [D_10,C_9,A_7,B_8] :
      ( r2_hidden(k1_funct_1(D_10,C_9),k2_relset_1(A_7,B_8,D_10))
      | k1_xboole_0 = B_8
      | ~ r2_hidden(C_9,A_7)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(D_10,A_7,B_8)
      | ~ v1_funct_1(D_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_65,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k3_funct_2(A_34,B_35,C_36,D_37) = k1_funct_1(C_36,D_37)
      | ~ m1_subset_1(D_37,A_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [B_35,C_36] :
      ( k3_funct_2('#skF_1',B_35,C_36,'#skF_3') = k1_funct_1(C_36,'#skF_3')
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_35)))
      | ~ v1_funct_2(C_36,'#skF_1',B_35)
      | ~ v1_funct_1(C_36)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_79,plain,(
    ! [B_38,C_39] :
      ( k3_funct_2('#skF_1',B_38,C_39,'#skF_3') = k1_funct_1(C_39,'#skF_3')
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_38)))
      | ~ v1_funct_2(C_39,'#skF_1',B_38)
      | ~ v1_funct_1(C_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_71])).

tff(c_86,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_79])).

tff(c_90,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_86])).

tff(c_16,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_16])).

tff(c_99,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_105,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_99])).

tff(c_109,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_112,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_115,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_115])).

tff(c_118,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_127,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:58:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.34  
% 1.88/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.34  
% 1.88/1.34  %Foreground sorts:
% 1.88/1.34  
% 1.88/1.34  
% 1.88/1.34  %Background operators:
% 1.88/1.34  
% 1.88/1.34  
% 1.88/1.34  %Foreground operators:
% 1.88/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.88/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.88/1.34  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.34  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.34  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.88/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.34  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.34  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 1.88/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.34  
% 2.13/1.35  tff(f_84, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.13/1.35  tff(f_39, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.13/1.35  tff(f_64, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.13/1.35  tff(f_52, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.13/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.13/1.35  tff(c_26, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.35  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.35  tff(c_24, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.35  tff(c_6, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.35  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.35  tff(c_20, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.35  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.35  tff(c_14, plain, (![D_10, C_9, A_7, B_8]: (r2_hidden(k1_funct_1(D_10, C_9), k2_relset_1(A_7, B_8, D_10)) | k1_xboole_0=B_8 | ~r2_hidden(C_9, A_7) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(D_10, A_7, B_8) | ~v1_funct_1(D_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.35  tff(c_65, plain, (![A_34, B_35, C_36, D_37]: (k3_funct_2(A_34, B_35, C_36, D_37)=k1_funct_1(C_36, D_37) | ~m1_subset_1(D_37, A_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.35  tff(c_71, plain, (![B_35, C_36]: (k3_funct_2('#skF_1', B_35, C_36, '#skF_3')=k1_funct_1(C_36, '#skF_3') | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_35))) | ~v1_funct_2(C_36, '#skF_1', B_35) | ~v1_funct_1(C_36) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_65])).
% 2.13/1.35  tff(c_79, plain, (![B_38, C_39]: (k3_funct_2('#skF_1', B_38, C_39, '#skF_3')=k1_funct_1(C_39, '#skF_3') | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_38))) | ~v1_funct_2(C_39, '#skF_1', B_38) | ~v1_funct_1(C_39))), inference(negUnitSimplification, [status(thm)], [c_28, c_71])).
% 2.13/1.35  tff(c_86, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_79])).
% 2.13/1.35  tff(c_90, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_86])).
% 2.13/1.35  tff(c_16, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.35  tff(c_92, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_16])).
% 2.13/1.35  tff(c_99, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_92])).
% 2.13/1.35  tff(c_105, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_99])).
% 2.13/1.35  tff(c_109, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_105])).
% 2.13/1.35  tff(c_112, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_109])).
% 2.13/1.35  tff(c_115, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_112])).
% 2.13/1.35  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_115])).
% 2.13/1.35  tff(c_118, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_105])).
% 2.13/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.13/1.35  tff(c_127, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2])).
% 2.13/1.35  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_127])).
% 2.13/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.35  
% 2.13/1.35  Inference rules
% 2.13/1.35  ----------------------
% 2.13/1.35  #Ref     : 0
% 2.13/1.35  #Sup     : 18
% 2.13/1.35  #Fact    : 0
% 2.13/1.35  #Define  : 0
% 2.13/1.35  #Split   : 4
% 2.13/1.35  #Chain   : 0
% 2.13/1.35  #Close   : 0
% 2.13/1.35  
% 2.13/1.35  Ordering : KBO
% 2.13/1.35  
% 2.13/1.35  Simplification rules
% 2.13/1.35  ----------------------
% 2.13/1.35  #Subsume      : 1
% 2.13/1.35  #Demod        : 10
% 2.13/1.35  #Tautology    : 5
% 2.13/1.35  #SimpNegUnit  : 5
% 2.13/1.35  #BackRed      : 4
% 2.13/1.35  
% 2.13/1.35  #Partial instantiations: 0
% 2.13/1.35  #Strategies tried      : 1
% 2.13/1.35  
% 2.13/1.35  Timing (in seconds)
% 2.13/1.35  ----------------------
% 2.13/1.36  Preprocessing        : 0.42
% 2.13/1.36  Parsing              : 0.25
% 2.13/1.36  CNF conversion       : 0.02
% 2.13/1.36  Main loop            : 0.15
% 2.13/1.36  Inferencing          : 0.05
% 2.13/1.36  Reduction            : 0.04
% 2.13/1.36  Demodulation         : 0.03
% 2.13/1.36  BG Simplification    : 0.01
% 2.13/1.36  Subsumption          : 0.03
% 2.13/1.36  Abstraction          : 0.01
% 2.13/1.36  MUC search           : 0.00
% 2.13/1.36  Cooper               : 0.00
% 2.13/1.36  Total                : 0.59
% 2.13/1.36  Index Insertion      : 0.00
% 2.13/1.36  Index Deletion       : 0.00
% 2.13/1.36  Index Matching       : 0.00
% 2.13/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
