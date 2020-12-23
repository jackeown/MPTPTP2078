%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:43 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 169 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_89,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_93,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_89])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_10])).

tff(c_99,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_96])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_59,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_41] :
      ( r1_tarski(A_41,'#skF_4')
      | ~ r1_tarski(A_41,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_78,plain,(
    ! [B_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,'#skF_2')),'#skF_4')
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_103,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_78])).

tff(c_110,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_103])).

tff(c_202,plain,(
    ! [B_58,A_59] :
      ( k7_relat_1(B_58,A_59) = B_58
      | ~ r1_tarski(k1_relat_1(B_58),A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_202])).

tff(c_232,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_214])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_236,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k2_partfun1(A_60,B_61,C_62,D_63) = k7_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_238,plain,(
    ! [D_63] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_63) = k7_relat_1('#skF_5',D_63)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_236])).

tff(c_241,plain,(
    ! [D_63] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_63) = k7_relat_1('#skF_5',D_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_238])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_276,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_28])).

tff(c_277,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_276])).

tff(c_34,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    ! [D_28,A_22,B_23,C_24] :
      ( k1_funct_1(D_28,'#skF_1'(A_22,B_23,C_24,D_28)) != k1_funct_1(C_24,'#skF_1'(A_22,B_23,C_24,D_28))
      | r2_relset_1(A_22,B_23,C_24,D_28)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(D_28,A_22,B_23)
      | ~ v1_funct_1(D_28)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_829,plain,(
    ! [A_107,B_108,C_109] :
      ( r2_relset_1(A_107,B_108,C_109,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_2(C_109,A_107,B_108)
      | ~ v1_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_2(C_109,A_107,B_108)
      | ~ v1_funct_1(C_109) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_24])).

tff(c_831,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_829])).

tff(c_834,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_831])).

tff(c_836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:56:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.46  
% 3.01/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.46  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.01/1.46  
% 3.01/1.46  %Foreground sorts:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Background operators:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Foreground operators:
% 3.01/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.01/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.01/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.01/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.01/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.46  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.01/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.01/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.01/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.46  
% 3.01/1.47  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 3.01/1.47  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.01/1.47  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.01/1.47  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.01/1.47  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.01/1.47  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.01/1.47  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.01/1.47  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.01/1.47  tff(f_89, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 3.01/1.47  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.01/1.47  tff(c_50, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.47  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_50])).
% 3.01/1.47  tff(c_89, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.01/1.47  tff(c_93, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_89])).
% 3.01/1.47  tff(c_10, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.01/1.47  tff(c_96, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_93, c_10])).
% 3.01/1.47  tff(c_99, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_96])).
% 3.01/1.47  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.01/1.47  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.01/1.47  tff(c_59, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.01/1.47  tff(c_69, plain, (![A_41]: (r1_tarski(A_41, '#skF_4') | ~r1_tarski(A_41, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_59])).
% 3.01/1.47  tff(c_78, plain, (![B_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, '#skF_2')), '#skF_4') | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_12, c_69])).
% 3.01/1.47  tff(c_103, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_99, c_78])).
% 3.01/1.47  tff(c_110, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_103])).
% 3.01/1.47  tff(c_202, plain, (![B_58, A_59]: (k7_relat_1(B_58, A_59)=B_58 | ~r1_tarski(k1_relat_1(B_58), A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.01/1.47  tff(c_214, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_202])).
% 3.01/1.47  tff(c_232, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_214])).
% 3.01/1.47  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.01/1.47  tff(c_236, plain, (![A_60, B_61, C_62, D_63]: (k2_partfun1(A_60, B_61, C_62, D_63)=k7_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.01/1.47  tff(c_238, plain, (![D_63]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_63)=k7_relat_1('#skF_5', D_63) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_236])).
% 3.01/1.47  tff(c_241, plain, (![D_63]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_63)=k7_relat_1('#skF_5', D_63))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_238])).
% 3.01/1.47  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.01/1.47  tff(c_276, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_28])).
% 3.01/1.47  tff(c_277, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_276])).
% 3.01/1.47  tff(c_34, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.01/1.47  tff(c_24, plain, (![D_28, A_22, B_23, C_24]: (k1_funct_1(D_28, '#skF_1'(A_22, B_23, C_24, D_28))!=k1_funct_1(C_24, '#skF_1'(A_22, B_23, C_24, D_28)) | r2_relset_1(A_22, B_23, C_24, D_28) | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(D_28, A_22, B_23) | ~v1_funct_1(D_28) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.01/1.47  tff(c_829, plain, (![A_107, B_108, C_109]: (r2_relset_1(A_107, B_108, C_109, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_2(C_109, A_107, B_108) | ~v1_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_2(C_109, A_107, B_108) | ~v1_funct_1(C_109))), inference(reflexivity, [status(thm), theory('equality')], [c_24])).
% 3.01/1.47  tff(c_831, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_829])).
% 3.01/1.47  tff(c_834, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_831])).
% 3.01/1.47  tff(c_836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_834])).
% 3.01/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  Inference rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Ref     : 1
% 3.01/1.47  #Sup     : 171
% 3.01/1.47  #Fact    : 0
% 3.01/1.47  #Define  : 0
% 3.01/1.47  #Split   : 4
% 3.01/1.47  #Chain   : 0
% 3.01/1.47  #Close   : 0
% 3.01/1.47  
% 3.01/1.47  Ordering : KBO
% 3.01/1.47  
% 3.01/1.47  Simplification rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Subsume      : 62
% 3.01/1.47  #Demod        : 116
% 3.01/1.47  #Tautology    : 34
% 3.01/1.47  #SimpNegUnit  : 2
% 3.01/1.47  #BackRed      : 1
% 3.01/1.47  
% 3.01/1.47  #Partial instantiations: 0
% 3.01/1.47  #Strategies tried      : 1
% 3.01/1.47  
% 3.01/1.47  Timing (in seconds)
% 3.01/1.47  ----------------------
% 3.01/1.48  Preprocessing        : 0.32
% 3.01/1.48  Parsing              : 0.18
% 3.01/1.48  CNF conversion       : 0.02
% 3.01/1.48  Main loop            : 0.35
% 3.01/1.48  Inferencing          : 0.13
% 3.01/1.48  Reduction            : 0.11
% 3.01/1.48  Demodulation         : 0.07
% 3.01/1.48  BG Simplification    : 0.02
% 3.01/1.48  Subsumption          : 0.08
% 3.01/1.48  Abstraction          : 0.02
% 3.01/1.48  MUC search           : 0.00
% 3.01/1.48  Cooper               : 0.00
% 3.01/1.48  Total                : 0.70
% 3.01/1.48  Index Insertion      : 0.00
% 3.01/1.48  Index Deletion       : 0.00
% 3.01/1.48  Index Matching       : 0.00
% 3.01/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
