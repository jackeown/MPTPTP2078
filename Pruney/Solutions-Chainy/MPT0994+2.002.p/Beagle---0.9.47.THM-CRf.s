%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 112 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 298 expanded)
%              Number of equality atoms :   24 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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
    ~ ! [A,B,C,D,E] :
        ( ( v1_funct_1(E)
          & v1_funct_2(E,A,B)
          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( r2_hidden(C,A)
            & r2_hidden(k1_funct_1(E,C),D) )
         => ( B = k1_xboole_0
            | k1_funct_1(k6_relset_1(A,B,D,E),C) = k1_funct_1(E,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
       => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_funct_1(k8_relat_1(A_6,B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_1,B_4] :
      ( k1_funct_1(A_1,B_4) = k1_xboole_0
      | r2_hidden(B_4,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_35,C_36,B_37] :
      ( r2_hidden(A_35,k1_relat_1(C_36))
      | ~ r2_hidden(A_35,k1_relat_1(k8_relat_1(B_37,C_36)))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_164,plain,(
    ! [B_55,C_56,B_57] :
      ( r2_hidden(B_55,k1_relat_1(C_56))
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56)
      | k1_funct_1(k8_relat_1(B_57,C_56),B_55) = k1_xboole_0
      | ~ v1_funct_1(k8_relat_1(B_57,C_56))
      | ~ v1_relat_1(k8_relat_1(B_57,C_56)) ) ),
    inference(resolution,[status(thm)],[c_8,c_61])).

tff(c_168,plain,(
    ! [B_58,B_59,A_60] :
      ( r2_hidden(B_58,k1_relat_1(B_59))
      | k1_funct_1(k8_relat_1(A_60,B_59),B_58) = k1_xboole_0
      | ~ v1_funct_1(k8_relat_1(A_60,B_59))
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_12,c_164])).

tff(c_172,plain,(
    ! [B_61,B_62,A_63] :
      ( r2_hidden(B_61,k1_relat_1(B_62))
      | k1_funct_1(k8_relat_1(A_63,B_62),B_61) = k1_xboole_0
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_10,c_168])).

tff(c_47,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k6_relset_1(A_30,B_31,C_32,D_33) = k8_relat_1(C_32,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ! [C_32] : k6_relset_1('#skF_1','#skF_2',C_32,'#skF_5') = k8_relat_1(C_32,'#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_26,plain,(
    k1_funct_1(k6_relset_1('#skF_1','#skF_2','#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_51,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_30,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_106,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden(A_49,k1_relat_1(k8_relat_1(B_50,C_51)))
      | ~ r2_hidden(k1_funct_1(C_51,A_49),B_50)
      | ~ r2_hidden(A_49,k1_relat_1(C_51))
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [B_12,C_13,A_11] :
      ( k1_funct_1(k8_relat_1(B_12,C_13),A_11) = k1_funct_1(C_13,A_11)
      | ~ r2_hidden(A_11,k1_relat_1(k8_relat_1(B_12,C_13)))
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_124,plain,(
    ! [B_52,C_53,A_54] :
      ( k1_funct_1(k8_relat_1(B_52,C_53),A_54) = k1_funct_1(C_53,A_54)
      | ~ r2_hidden(k1_funct_1(C_53,A_54),B_52)
      | ~ r2_hidden(A_54,k1_relat_1(C_53))
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_106,c_20])).

tff(c_135,plain,
    ( k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_140,plain,
    ( k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_135])).

tff(c_141,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_140])).

tff(c_175,plain,(
    ! [A_63] :
      ( k1_funct_1(k8_relat_1(A_63,'#skF_5'),'#skF_3') = k1_xboole_0
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_172,c_141])).

tff(c_211,plain,(
    ! [A_63] : k1_funct_1(k8_relat_1(A_63,'#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_175])).

tff(c_144,plain,
    ( k1_funct_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_147,plain,(
    k1_funct_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_144])).

tff(c_148,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_51])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:13:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.32  
% 1.89/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.32  
% 2.21/1.32  %Foreground sorts:
% 2.21/1.32  
% 2.21/1.32  
% 2.21/1.32  %Background operators:
% 2.21/1.32  
% 2.21/1.32  
% 2.21/1.32  %Foreground operators:
% 2.21/1.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.21/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.21/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.32  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.32  
% 2.21/1.34  tff(f_92, negated_conjecture, ~(![A, B, C, D, E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((r2_hidden(C, A) & r2_hidden(k1_funct_1(E, C), D)) => ((B = k1_xboole_0) | (k1_funct_1(k6_relset_1(A, B, D, E), C) = k1_funct_1(E, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_funct_2)).
% 2.21/1.34  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.21/1.34  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 2.21/1.34  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.21/1.34  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 2.21/1.34  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.21/1.34  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 2.21/1.34  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.34  tff(c_40, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.21/1.34  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_40])).
% 2.21/1.34  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.34  tff(c_10, plain, (![A_6, B_7]: (v1_funct_1(k8_relat_1(A_6, B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.34  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.34  tff(c_8, plain, (![A_1, B_4]: (k1_funct_1(A_1, B_4)=k1_xboole_0 | r2_hidden(B_4, k1_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.34  tff(c_61, plain, (![A_35, C_36, B_37]: (r2_hidden(A_35, k1_relat_1(C_36)) | ~r2_hidden(A_35, k1_relat_1(k8_relat_1(B_37, C_36))) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.34  tff(c_164, plain, (![B_55, C_56, B_57]: (r2_hidden(B_55, k1_relat_1(C_56)) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56) | k1_funct_1(k8_relat_1(B_57, C_56), B_55)=k1_xboole_0 | ~v1_funct_1(k8_relat_1(B_57, C_56)) | ~v1_relat_1(k8_relat_1(B_57, C_56)))), inference(resolution, [status(thm)], [c_8, c_61])).
% 2.21/1.34  tff(c_168, plain, (![B_58, B_59, A_60]: (r2_hidden(B_58, k1_relat_1(B_59)) | k1_funct_1(k8_relat_1(A_60, B_59), B_58)=k1_xboole_0 | ~v1_funct_1(k8_relat_1(A_60, B_59)) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_12, c_164])).
% 2.21/1.34  tff(c_172, plain, (![B_61, B_62, A_63]: (r2_hidden(B_61, k1_relat_1(B_62)) | k1_funct_1(k8_relat_1(A_63, B_62), B_61)=k1_xboole_0 | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_10, c_168])).
% 2.21/1.34  tff(c_47, plain, (![A_30, B_31, C_32, D_33]: (k6_relset_1(A_30, B_31, C_32, D_33)=k8_relat_1(C_32, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.34  tff(c_50, plain, (![C_32]: (k6_relset_1('#skF_1', '#skF_2', C_32, '#skF_5')=k8_relat_1(C_32, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_47])).
% 2.21/1.34  tff(c_26, plain, (k1_funct_1(k6_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.34  tff(c_51, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 2.21/1.34  tff(c_30, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.34  tff(c_106, plain, (![A_49, B_50, C_51]: (r2_hidden(A_49, k1_relat_1(k8_relat_1(B_50, C_51))) | ~r2_hidden(k1_funct_1(C_51, A_49), B_50) | ~r2_hidden(A_49, k1_relat_1(C_51)) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.34  tff(c_20, plain, (![B_12, C_13, A_11]: (k1_funct_1(k8_relat_1(B_12, C_13), A_11)=k1_funct_1(C_13, A_11) | ~r2_hidden(A_11, k1_relat_1(k8_relat_1(B_12, C_13))) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.34  tff(c_124, plain, (![B_52, C_53, A_54]: (k1_funct_1(k8_relat_1(B_52, C_53), A_54)=k1_funct_1(C_53, A_54) | ~r2_hidden(k1_funct_1(C_53, A_54), B_52) | ~r2_hidden(A_54, k1_relat_1(C_53)) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_106, c_20])).
% 2.21/1.34  tff(c_135, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_124])).
% 2.21/1.34  tff(c_140, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_135])).
% 2.21/1.34  tff(c_141, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_51, c_140])).
% 2.21/1.34  tff(c_175, plain, (![A_63]: (k1_funct_1(k8_relat_1(A_63, '#skF_5'), '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_172, c_141])).
% 2.21/1.34  tff(c_211, plain, (![A_63]: (k1_funct_1(k8_relat_1(A_63, '#skF_5'), '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_175])).
% 2.21/1.34  tff(c_144, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_141])).
% 2.21/1.34  tff(c_147, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_144])).
% 2.21/1.34  tff(c_148, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_147, c_51])).
% 2.21/1.34  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_148])).
% 2.21/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  Inference rules
% 2.21/1.34  ----------------------
% 2.21/1.34  #Ref     : 0
% 2.21/1.34  #Sup     : 36
% 2.21/1.34  #Fact    : 0
% 2.21/1.34  #Define  : 0
% 2.21/1.34  #Split   : 0
% 2.21/1.34  #Chain   : 0
% 2.21/1.34  #Close   : 0
% 2.21/1.34  
% 2.21/1.34  Ordering : KBO
% 2.21/1.34  
% 2.21/1.34  Simplification rules
% 2.21/1.34  ----------------------
% 2.21/1.34  #Subsume      : 7
% 2.21/1.34  #Demod        : 15
% 2.21/1.34  #Tautology    : 9
% 2.21/1.34  #SimpNegUnit  : 1
% 2.21/1.34  #BackRed      : 4
% 2.21/1.34  
% 2.21/1.34  #Partial instantiations: 0
% 2.21/1.34  #Strategies tried      : 1
% 2.21/1.34  
% 2.21/1.34  Timing (in seconds)
% 2.21/1.34  ----------------------
% 2.21/1.34  Preprocessing        : 0.32
% 2.21/1.34  Parsing              : 0.17
% 2.21/1.34  CNF conversion       : 0.02
% 2.21/1.34  Main loop            : 0.20
% 2.21/1.34  Inferencing          : 0.08
% 2.21/1.34  Reduction            : 0.06
% 2.21/1.34  Demodulation         : 0.04
% 2.21/1.34  BG Simplification    : 0.01
% 2.21/1.34  Subsumption          : 0.04
% 2.21/1.34  Abstraction          : 0.01
% 2.21/1.34  MUC search           : 0.00
% 2.21/1.34  Cooper               : 0.00
% 2.21/1.34  Total                : 0.55
% 2.21/1.34  Index Insertion      : 0.00
% 2.21/1.34  Index Deletion       : 0.00
% 2.21/1.34  Index Matching       : 0.00
% 2.21/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
