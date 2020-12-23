%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:04 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 129 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_37,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_43,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_63,plain,(
    ! [C_37,B_38,A_39] :
      ( v5_relat_1(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_63])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_100,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_109,plain,(
    ! [D_55,C_56,A_57,B_58] :
      ( r2_hidden(k1_funct_1(D_55,C_56),k2_relset_1(A_57,B_58,D_55))
      | k1_xboole_0 = B_58
      | ~ r2_hidden(C_56,A_57)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(D_55,A_57,B_58)
      | ~ v1_funct_1(D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_114,plain,(
    ! [C_56] :
      ( r2_hidden(k1_funct_1('#skF_5',C_56),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_56,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_109])).

tff(c_117,plain,(
    ! [C_56] :
      ( r2_hidden(k1_funct_1('#skF_5',C_56),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_56,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_114])).

tff(c_119,plain,(
    ! [C_59] :
      ( r2_hidden(k1_funct_1('#skF_5',C_59),k2_relat_1('#skF_5'))
      | ~ r2_hidden(C_59,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_117])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [C_62,B_63] :
      ( r2_hidden(k1_funct_1('#skF_5',C_62),B_63)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_63)
      | ~ r2_hidden(C_62,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_24,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_129,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3')
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_24])).

tff(c_133,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_129])).

tff(c_136,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_67,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.99/1.16  
% 1.99/1.16  %Foreground sorts:
% 1.99/1.16  
% 1.99/1.16  
% 1.99/1.16  %Background operators:
% 1.99/1.16  
% 1.99/1.16  
% 1.99/1.16  %Foreground operators:
% 1.99/1.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.99/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.99/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.99/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.99/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.16  
% 1.99/1.17  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.99/1.17  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.99/1.17  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.99/1.17  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.99/1.17  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.99/1.17  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.99/1.17  tff(f_69, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 1.99/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.99/1.17  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.17  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.99/1.17  tff(c_37, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.17  tff(c_40, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_37])).
% 1.99/1.17  tff(c_43, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 1.99/1.17  tff(c_63, plain, (![C_37, B_38, A_39]: (v5_relat_1(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_38))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.17  tff(c_67, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_63])).
% 1.99/1.17  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.17  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.99/1.17  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.99/1.17  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.99/1.17  tff(c_32, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.99/1.17  tff(c_100, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.17  tff(c_104, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_100])).
% 1.99/1.17  tff(c_109, plain, (![D_55, C_56, A_57, B_58]: (r2_hidden(k1_funct_1(D_55, C_56), k2_relset_1(A_57, B_58, D_55)) | k1_xboole_0=B_58 | ~r2_hidden(C_56, A_57) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(D_55, A_57, B_58) | ~v1_funct_1(D_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.17  tff(c_114, plain, (![C_56]: (r2_hidden(k1_funct_1('#skF_5', C_56), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_56, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_109])).
% 1.99/1.17  tff(c_117, plain, (![C_56]: (r2_hidden(k1_funct_1('#skF_5', C_56), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_56, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_114])).
% 1.99/1.17  tff(c_119, plain, (![C_59]: (r2_hidden(k1_funct_1('#skF_5', C_59), k2_relat_1('#skF_5')) | ~r2_hidden(C_59, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_117])).
% 1.99/1.17  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.17  tff(c_124, plain, (![C_62, B_63]: (r2_hidden(k1_funct_1('#skF_5', C_62), B_63) | ~r1_tarski(k2_relat_1('#skF_5'), B_63) | ~r2_hidden(C_62, '#skF_2'))), inference(resolution, [status(thm)], [c_119, c_2])).
% 1.99/1.17  tff(c_24, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.99/1.17  tff(c_129, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3') | ~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_124, c_24])).
% 1.99/1.17  tff(c_133, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_129])).
% 1.99/1.17  tff(c_136, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_133])).
% 1.99/1.17  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_67, c_136])).
% 1.99/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.17  
% 1.99/1.17  Inference rules
% 1.99/1.17  ----------------------
% 1.99/1.17  #Ref     : 0
% 1.99/1.17  #Sup     : 22
% 1.99/1.17  #Fact    : 0
% 1.99/1.17  #Define  : 0
% 1.99/1.17  #Split   : 0
% 1.99/1.17  #Chain   : 0
% 1.99/1.17  #Close   : 0
% 1.99/1.17  
% 1.99/1.17  Ordering : KBO
% 1.99/1.17  
% 1.99/1.17  Simplification rules
% 1.99/1.17  ----------------------
% 1.99/1.17  #Subsume      : 1
% 1.99/1.17  #Demod        : 7
% 1.99/1.17  #Tautology    : 4
% 1.99/1.17  #SimpNegUnit  : 1
% 1.99/1.17  #BackRed      : 0
% 1.99/1.17  
% 1.99/1.17  #Partial instantiations: 0
% 1.99/1.17  #Strategies tried      : 1
% 1.99/1.17  
% 1.99/1.17  Timing (in seconds)
% 1.99/1.17  ----------------------
% 1.99/1.18  Preprocessing        : 0.30
% 1.99/1.18  Parsing              : 0.17
% 1.99/1.18  CNF conversion       : 0.02
% 1.99/1.18  Main loop            : 0.15
% 1.99/1.18  Inferencing          : 0.06
% 1.99/1.18  Reduction            : 0.04
% 1.99/1.18  Demodulation         : 0.03
% 1.99/1.18  BG Simplification    : 0.01
% 1.99/1.18  Subsumption          : 0.03
% 1.99/1.18  Abstraction          : 0.01
% 1.99/1.18  MUC search           : 0.00
% 1.99/1.18  Cooper               : 0.00
% 1.99/1.18  Total                : 0.48
% 1.99/1.18  Index Insertion      : 0.00
% 1.99/1.18  Index Deletion       : 0.00
% 1.99/1.18  Index Matching       : 0.00
% 1.99/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
