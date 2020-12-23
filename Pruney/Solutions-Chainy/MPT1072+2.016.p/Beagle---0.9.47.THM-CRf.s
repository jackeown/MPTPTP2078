%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:57 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   48 (  93 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 274 expanded)
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

tff(f_77,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_45,axiom,(
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

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [D_10,C_9,A_7,B_8] :
      ( r2_hidden(k1_funct_1(D_10,C_9),k2_relset_1(A_7,B_8,D_10))
      | k1_xboole_0 = B_8
      | ~ r2_hidden(C_9,A_7)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(D_10,A_7,B_8)
      | ~ v1_funct_1(D_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( k3_funct_2(A_28,B_29,C_30,D_31) = k1_funct_1(C_30,D_31)
      | ~ m1_subset_1(D_31,A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [B_29,C_30] :
      ( k3_funct_2('#skF_1',B_29,C_30,'#skF_3') = k1_funct_1(C_30,'#skF_3')
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_29)))
      | ~ v1_funct_2(C_30,'#skF_1',B_29)
      | ~ v1_funct_1(C_30)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_39,plain,(
    ! [B_32,C_33] :
      ( k3_funct_2('#skF_1',B_32,C_33,'#skF_3') = k1_funct_1(C_33,'#skF_3')
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_32)))
      | ~ v1_funct_2(C_33,'#skF_1',B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_34])).

tff(c_42,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_45,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_42])).

tff(c_10,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_10])).

tff(c_55,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_61,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_55])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_67,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_70,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_67])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_70])).

tff(c_73,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_76,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:59:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.38  
% 2.11/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.11/1.39  
% 2.11/1.39  %Foreground sorts:
% 2.11/1.39  
% 2.11/1.39  
% 2.11/1.39  %Background operators:
% 2.11/1.39  
% 2.11/1.39  
% 2.11/1.39  %Foreground operators:
% 2.11/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.11/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.39  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.11/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.39  
% 2.11/1.40  tff(f_77, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.11/1.40  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.11/1.40  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.11/1.40  tff(f_45, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.11/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.11/1.40  tff(c_20, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.40  tff(c_22, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.40  tff(c_18, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.40  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.11/1.40  tff(c_16, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.40  tff(c_14, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.40  tff(c_12, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.40  tff(c_8, plain, (![D_10, C_9, A_7, B_8]: (r2_hidden(k1_funct_1(D_10, C_9), k2_relset_1(A_7, B_8, D_10)) | k1_xboole_0=B_8 | ~r2_hidden(C_9, A_7) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(D_10, A_7, B_8) | ~v1_funct_1(D_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.40  tff(c_30, plain, (![A_28, B_29, C_30, D_31]: (k3_funct_2(A_28, B_29, C_30, D_31)=k1_funct_1(C_30, D_31) | ~m1_subset_1(D_31, A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.40  tff(c_34, plain, (![B_29, C_30]: (k3_funct_2('#skF_1', B_29, C_30, '#skF_3')=k1_funct_1(C_30, '#skF_3') | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_29))) | ~v1_funct_2(C_30, '#skF_1', B_29) | ~v1_funct_1(C_30) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_30])).
% 2.11/1.40  tff(c_39, plain, (![B_32, C_33]: (k3_funct_2('#skF_1', B_32, C_33, '#skF_3')=k1_funct_1(C_33, '#skF_3') | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_32))) | ~v1_funct_2(C_33, '#skF_1', B_32) | ~v1_funct_1(C_33))), inference(negUnitSimplification, [status(thm)], [c_22, c_34])).
% 2.11/1.40  tff(c_42, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_39])).
% 2.11/1.40  tff(c_45, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_42])).
% 2.11/1.40  tff(c_10, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.40  tff(c_47, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_10])).
% 2.11/1.40  tff(c_55, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_47])).
% 2.11/1.40  tff(c_61, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_55])).
% 2.11/1.40  tff(c_63, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_61])).
% 2.11/1.40  tff(c_67, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_4, c_63])).
% 2.11/1.40  tff(c_70, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_67])).
% 2.11/1.40  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_70])).
% 2.11/1.40  tff(c_73, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_61])).
% 2.11/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.11/1.40  tff(c_76, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2])).
% 2.11/1.40  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_76])).
% 2.11/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.40  
% 2.11/1.40  Inference rules
% 2.11/1.40  ----------------------
% 2.11/1.40  #Ref     : 0
% 2.11/1.40  #Sup     : 9
% 2.11/1.40  #Fact    : 0
% 2.11/1.40  #Define  : 0
% 2.11/1.40  #Split   : 4
% 2.11/1.40  #Chain   : 0
% 2.11/1.40  #Close   : 0
% 2.11/1.40  
% 2.11/1.40  Ordering : KBO
% 2.11/1.40  
% 2.11/1.40  Simplification rules
% 2.11/1.40  ----------------------
% 2.11/1.40  #Subsume      : 0
% 2.11/1.40  #Demod        : 10
% 2.11/1.40  #Tautology    : 2
% 2.11/1.40  #SimpNegUnit  : 3
% 2.11/1.40  #BackRed      : 4
% 2.11/1.40  
% 2.11/1.40  #Partial instantiations: 0
% 2.11/1.40  #Strategies tried      : 1
% 2.11/1.40  
% 2.11/1.40  Timing (in seconds)
% 2.11/1.40  ----------------------
% 2.11/1.40  Preprocessing        : 0.47
% 2.11/1.40  Parsing              : 0.25
% 2.11/1.40  CNF conversion       : 0.03
% 2.11/1.40  Main loop            : 0.14
% 2.11/1.40  Inferencing          : 0.05
% 2.11/1.40  Reduction            : 0.04
% 2.11/1.40  Demodulation         : 0.03
% 2.11/1.41  BG Simplification    : 0.01
% 2.11/1.41  Subsumption          : 0.02
% 2.11/1.41  Abstraction          : 0.01
% 2.11/1.41  MUC search           : 0.00
% 2.11/1.41  Cooper               : 0.00
% 2.11/1.41  Total                : 0.65
% 2.11/1.41  Index Insertion      : 0.00
% 2.11/1.41  Index Deletion       : 0.00
% 2.11/1.41  Index Matching       : 0.00
% 2.11/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
