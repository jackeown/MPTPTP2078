%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:14 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   65 (  88 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 101 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_36,B_37] :
      ( r2_hidden(A_36,B_37)
      | v1_xboole_0(B_37)
      | ~ m1_subset_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [A_36,A_1] :
      ( r1_tarski(A_36,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_36,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_92,plain,(
    ! [A_38,A_39] :
      ( r1_tarski(A_38,A_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(A_39)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_88])).

tff(c_100,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_92])).

tff(c_36,plain,(
    ! [A_24] : k6_relat_1(A_24) = k6_partfun1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [A_10] : v1_relat_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22])).

tff(c_24,plain,(
    ! [A_10] : v1_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [A_10] : v1_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24])).

tff(c_34,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_146,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k8_relset_1(A_52,B_53,C_54,D_55) = k10_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_149,plain,(
    ! [A_23,D_55] : k8_relset_1(A_23,A_23,k6_partfun1(A_23),D_55) = k10_relat_1(k6_partfun1(A_23),D_55) ),
    inference(resolution,[status(thm)],[c_41,c_146])).

tff(c_160,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( m1_subset_1(k8_relset_1(A_58,B_59,C_60,D_61),k1_zfmisc_1(A_58))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_172,plain,(
    ! [A_23,D_55] :
      ( m1_subset_1(k10_relat_1(k6_partfun1(A_23),D_55),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_160])).

tff(c_178,plain,(
    ! [A_62,D_63] : m1_subset_1(k10_relat_1(k6_partfun1(A_62),D_63),k1_zfmisc_1(A_62)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_172])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( k9_relat_1(k6_relat_1(A_13),B_14) = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_13,B_14] :
      ( k9_relat_1(k6_partfun1(A_13),B_14) = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28])).

tff(c_189,plain,(
    ! [A_62,D_63] : k9_relat_1(k6_partfun1(A_62),k10_relat_1(k6_partfun1(A_62),D_63)) = k10_relat_1(k6_partfun1(A_62),D_63) ),
    inference(resolution,[status(thm)],[c_178,c_42])).

tff(c_20,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    ! [A_9] : k2_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20])).

tff(c_201,plain,(
    ! [B_68,A_69] :
      ( k9_relat_1(B_68,k10_relat_1(B_68,A_69)) = A_69
      | ~ r1_tarski(A_69,k2_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_209,plain,(
    ! [A_9,A_69] :
      ( k9_relat_1(k6_partfun1(A_9),k10_relat_1(k6_partfun1(A_9),A_69)) = A_69
      | ~ r1_tarski(A_69,A_9)
      | ~ v1_funct_1(k6_partfun1(A_9))
      | ~ v1_relat_1(k6_partfun1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_201])).

tff(c_214,plain,(
    ! [A_70,A_71] :
      ( k10_relat_1(k6_partfun1(A_70),A_71) = A_71
      | ~ r1_tarski(A_71,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_43,c_189,c_209])).

tff(c_38,plain,(
    k8_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_150,plain,(
    k10_relat_1(k6_partfun1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_38])).

tff(c_229,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_150])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.98/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.98/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.23  
% 2.16/1.24  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 2.16/1.24  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.16/1.24  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.16/1.24  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.16/1.24  tff(f_73, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.16/1.24  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.16/1.24  tff(f_71, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.16/1.24  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.16/1.24  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.16/1.24  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.16/1.24  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.16/1.24  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.16/1.24  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.24  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.24  tff(c_84, plain, (![A_36, B_37]: (r2_hidden(A_36, B_37) | v1_xboole_0(B_37) | ~m1_subset_1(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.24  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.24  tff(c_88, plain, (![A_36, A_1]: (r1_tarski(A_36, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_36, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_84, c_2])).
% 2.16/1.24  tff(c_92, plain, (![A_38, A_39]: (r1_tarski(A_38, A_39) | ~m1_subset_1(A_38, k1_zfmisc_1(A_39)))), inference(negUnitSimplification, [status(thm)], [c_14, c_88])).
% 2.16/1.24  tff(c_100, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_92])).
% 2.16/1.24  tff(c_36, plain, (![A_24]: (k6_relat_1(A_24)=k6_partfun1(A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.24  tff(c_22, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.24  tff(c_44, plain, (![A_10]: (v1_relat_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22])).
% 2.16/1.24  tff(c_24, plain, (![A_10]: (v1_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.24  tff(c_43, plain, (![A_10]: (v1_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24])).
% 2.16/1.24  tff(c_34, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.24  tff(c_41, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 2.16/1.24  tff(c_146, plain, (![A_52, B_53, C_54, D_55]: (k8_relset_1(A_52, B_53, C_54, D_55)=k10_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.16/1.24  tff(c_149, plain, (![A_23, D_55]: (k8_relset_1(A_23, A_23, k6_partfun1(A_23), D_55)=k10_relat_1(k6_partfun1(A_23), D_55))), inference(resolution, [status(thm)], [c_41, c_146])).
% 2.16/1.24  tff(c_160, plain, (![A_58, B_59, C_60, D_61]: (m1_subset_1(k8_relset_1(A_58, B_59, C_60, D_61), k1_zfmisc_1(A_58)) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.24  tff(c_172, plain, (![A_23, D_55]: (m1_subset_1(k10_relat_1(k6_partfun1(A_23), D_55), k1_zfmisc_1(A_23)) | ~m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(superposition, [status(thm), theory('equality')], [c_149, c_160])).
% 2.16/1.24  tff(c_178, plain, (![A_62, D_63]: (m1_subset_1(k10_relat_1(k6_partfun1(A_62), D_63), k1_zfmisc_1(A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_172])).
% 2.16/1.24  tff(c_28, plain, (![A_13, B_14]: (k9_relat_1(k6_relat_1(A_13), B_14)=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.24  tff(c_42, plain, (![A_13, B_14]: (k9_relat_1(k6_partfun1(A_13), B_14)=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28])).
% 2.16/1.24  tff(c_189, plain, (![A_62, D_63]: (k9_relat_1(k6_partfun1(A_62), k10_relat_1(k6_partfun1(A_62), D_63))=k10_relat_1(k6_partfun1(A_62), D_63))), inference(resolution, [status(thm)], [c_178, c_42])).
% 2.16/1.24  tff(c_20, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.24  tff(c_45, plain, (![A_9]: (k2_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_20])).
% 2.16/1.24  tff(c_201, plain, (![B_68, A_69]: (k9_relat_1(B_68, k10_relat_1(B_68, A_69))=A_69 | ~r1_tarski(A_69, k2_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.24  tff(c_209, plain, (![A_9, A_69]: (k9_relat_1(k6_partfun1(A_9), k10_relat_1(k6_partfun1(A_9), A_69))=A_69 | ~r1_tarski(A_69, A_9) | ~v1_funct_1(k6_partfun1(A_9)) | ~v1_relat_1(k6_partfun1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_201])).
% 2.16/1.24  tff(c_214, plain, (![A_70, A_71]: (k10_relat_1(k6_partfun1(A_70), A_71)=A_71 | ~r1_tarski(A_71, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_43, c_189, c_209])).
% 2.16/1.24  tff(c_38, plain, (k8_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.24  tff(c_150, plain, (k10_relat_1(k6_partfun1('#skF_3'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_38])).
% 2.16/1.24  tff(c_229, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_214, c_150])).
% 2.16/1.24  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_229])).
% 2.16/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  Inference rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Ref     : 0
% 2.16/1.24  #Sup     : 41
% 2.16/1.24  #Fact    : 0
% 2.16/1.24  #Define  : 0
% 2.16/1.24  #Split   : 0
% 2.16/1.24  #Chain   : 0
% 2.16/1.24  #Close   : 0
% 2.16/1.24  
% 2.16/1.24  Ordering : KBO
% 2.16/1.24  
% 2.16/1.24  Simplification rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Subsume      : 0
% 2.16/1.24  #Demod        : 12
% 2.16/1.24  #Tautology    : 17
% 2.16/1.24  #SimpNegUnit  : 1
% 2.16/1.24  #BackRed      : 1
% 2.16/1.24  
% 2.16/1.24  #Partial instantiations: 0
% 2.16/1.24  #Strategies tried      : 1
% 2.16/1.24  
% 2.16/1.24  Timing (in seconds)
% 2.16/1.24  ----------------------
% 2.16/1.24  Preprocessing        : 0.31
% 2.16/1.24  Parsing              : 0.16
% 2.16/1.25  CNF conversion       : 0.02
% 2.16/1.25  Main loop            : 0.18
% 2.16/1.25  Inferencing          : 0.07
% 2.16/1.25  Reduction            : 0.06
% 2.16/1.25  Demodulation         : 0.04
% 2.16/1.25  BG Simplification    : 0.01
% 2.16/1.25  Subsumption          : 0.02
% 2.16/1.25  Abstraction          : 0.01
% 2.16/1.25  MUC search           : 0.00
% 2.16/1.25  Cooper               : 0.00
% 2.16/1.25  Total                : 0.52
% 2.16/1.25  Index Insertion      : 0.00
% 2.16/1.25  Index Deletion       : 0.00
% 2.16/1.25  Index Matching       : 0.00
% 2.16/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
