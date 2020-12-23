%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:07 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 144 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_43])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_36,B_37,C_38] :
      ( k1_relset_1(A_36,B_37,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_141,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_57,B_56,C_58) = A_57
      | ~ v1_funct_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_141])).

tff(c_152,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_66,c_148])).

tff(c_153,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_152])).

tff(c_53,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_relset_1(A_33,B_34,C_35) = k2_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_57,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_67,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k2_relset_1(A_39,B_40,C_41),k1_zfmisc_1(B_40))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_81,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_67])).

tff(c_86,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81])).

tff(c_107,plain,(
    ! [B_45,A_46] :
      ( r2_hidden(k1_funct_1(B_45,A_46),k2_relat_1(B_45))
      | ~ r2_hidden(A_46,k1_relat_1(B_45))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,(
    ! [B_59,A_60,A_61] :
      ( r2_hidden(k1_funct_1(B_59,A_60),A_61)
      | ~ m1_subset_1(k2_relat_1(B_59),k1_zfmisc_1(A_61))
      | ~ r2_hidden(A_60,k1_relat_1(B_59))
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_165,plain,(
    ! [A_60] :
      ( r2_hidden(k1_funct_1('#skF_4',A_60),'#skF_2')
      | ~ r2_hidden(A_60,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_163])).

tff(c_169,plain,(
    ! [A_62] :
      ( r2_hidden(k1_funct_1('#skF_4',A_62),'#skF_2')
      | ~ r2_hidden(A_62,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_153,c_165])).

tff(c_28,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_174,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_169,c_28])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.37  
% 2.24/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.38  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.38  
% 2.24/1.38  %Foreground sorts:
% 2.24/1.38  
% 2.24/1.38  
% 2.24/1.38  %Background operators:
% 2.24/1.38  
% 2.24/1.38  
% 2.24/1.38  %Foreground operators:
% 2.24/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.38  
% 2.24/1.39  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.24/1.39  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.24/1.39  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.24/1.39  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.24/1.39  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.24/1.39  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.24/1.39  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.24/1.39  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.24/1.39  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.24/1.39  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.39  tff(c_6, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.39  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.39  tff(c_40, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.39  tff(c_43, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_40])).
% 2.24/1.39  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_43])).
% 2.24/1.39  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.39  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.39  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.39  tff(c_62, plain, (![A_36, B_37, C_38]: (k1_relset_1(A_36, B_37, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.39  tff(c_66, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.24/1.39  tff(c_141, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_relset_1(A_57, B_56, C_58)=A_57 | ~v1_funct_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.39  tff(c_148, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_141])).
% 2.24/1.39  tff(c_152, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_66, c_148])).
% 2.24/1.39  tff(c_153, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30, c_152])).
% 2.24/1.39  tff(c_53, plain, (![A_33, B_34, C_35]: (k2_relset_1(A_33, B_34, C_35)=k2_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.24/1.39  tff(c_57, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_53])).
% 2.24/1.39  tff(c_67, plain, (![A_39, B_40, C_41]: (m1_subset_1(k2_relset_1(A_39, B_40, C_41), k1_zfmisc_1(B_40)) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.39  tff(c_81, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_57, c_67])).
% 2.24/1.39  tff(c_86, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81])).
% 2.24/1.39  tff(c_107, plain, (![B_45, A_46]: (r2_hidden(k1_funct_1(B_45, A_46), k2_relat_1(B_45)) | ~r2_hidden(A_46, k1_relat_1(B_45)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.39  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.39  tff(c_163, plain, (![B_59, A_60, A_61]: (r2_hidden(k1_funct_1(B_59, A_60), A_61) | ~m1_subset_1(k2_relat_1(B_59), k1_zfmisc_1(A_61)) | ~r2_hidden(A_60, k1_relat_1(B_59)) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.24/1.39  tff(c_165, plain, (![A_60]: (r2_hidden(k1_funct_1('#skF_4', A_60), '#skF_2') | ~r2_hidden(A_60, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_86, c_163])).
% 2.24/1.39  tff(c_169, plain, (![A_62]: (r2_hidden(k1_funct_1('#skF_4', A_62), '#skF_2') | ~r2_hidden(A_62, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_153, c_165])).
% 2.24/1.39  tff(c_28, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.39  tff(c_174, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_169, c_28])).
% 2.24/1.39  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_174])).
% 2.24/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.39  
% 2.24/1.39  Inference rules
% 2.24/1.39  ----------------------
% 2.24/1.39  #Ref     : 0
% 2.24/1.39  #Sup     : 30
% 2.24/1.39  #Fact    : 0
% 2.24/1.39  #Define  : 0
% 2.24/1.39  #Split   : 1
% 2.24/1.39  #Chain   : 0
% 2.24/1.39  #Close   : 0
% 2.24/1.39  
% 2.24/1.39  Ordering : KBO
% 2.24/1.39  
% 2.24/1.39  Simplification rules
% 2.24/1.39  ----------------------
% 2.24/1.39  #Subsume      : 1
% 2.24/1.39  #Demod        : 12
% 2.24/1.39  #Tautology    : 9
% 2.24/1.39  #SimpNegUnit  : 2
% 2.24/1.39  #BackRed      : 1
% 2.24/1.39  
% 2.24/1.39  #Partial instantiations: 0
% 2.24/1.39  #Strategies tried      : 1
% 2.24/1.39  
% 2.24/1.39  Timing (in seconds)
% 2.24/1.39  ----------------------
% 2.41/1.39  Preprocessing        : 0.49
% 2.41/1.39  Parsing              : 0.30
% 2.41/1.39  CNF conversion       : 0.03
% 2.41/1.39  Main loop            : 0.19
% 2.41/1.39  Inferencing          : 0.07
% 2.41/1.39  Reduction            : 0.06
% 2.41/1.39  Demodulation         : 0.04
% 2.41/1.39  BG Simplification    : 0.02
% 2.41/1.39  Subsumption          : 0.04
% 2.41/1.40  Abstraction          : 0.01
% 2.41/1.40  MUC search           : 0.00
% 2.41/1.40  Cooper               : 0.00
% 2.41/1.40  Total                : 0.72
% 2.41/1.40  Index Insertion      : 0.00
% 2.41/1.40  Index Deletion       : 0.00
% 2.41/1.40  Index Matching       : 0.00
% 2.41/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
